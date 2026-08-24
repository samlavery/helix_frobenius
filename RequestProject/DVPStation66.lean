import RequestProject.DVPSqrtTable

/-!
# Station `t = 66` of the extended Hardy ladder (rung-74)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT66 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((66 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((233983/1000000 : ℚ) : ℝ))

theorem st66_c1 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((972751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -292479/5000000) (δ := 21/100000000) (ψ := 233983/1000000) 66 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t1 : ((972701/1000000 : ℚ) : ℝ) ≤ stT66 1 := by
  have hc : ((972701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((972701/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((972701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c2 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((39353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 478573/1250000) (δ := 517/100000000) (ψ := 233983/1000000) 66 7
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t2 : ((277914146301/10000000000000 : ℚ) : ℝ) ≤ stT66 2 := by
  have hc : ((39303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((277914146301/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((39303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c3 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-499921/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -780949/1000000) (δ := 11/2000000) (ψ := 233983/1000000) 66 12
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t3 : ((-1443219865419/2500000000000 : ℚ) : ℝ) ≤ stT66 3 := by
  have hc : ((-249973/250000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1443219865419/2500000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-249973/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c4 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-246993/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7465837/10000000) (δ := 201/50000000) (ψ := 233983/1000000) 66 15
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t4 : ((-2470055494011/5000000000000 : ℚ) : ℝ) ≤ stT66 4 := by
  have hc : ((-494011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2470055494011/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-494011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c5 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((678387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1031539/5000000) (δ := 599/100000000) (ψ := 233983/1000000) 66 17
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t5 : ((606722927899/2000000000000 : ℚ) : ℝ) ≤ stT66 5 := by
  have hc : ((678337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((606722927899/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((678337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c6 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((210823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -848987/2500000) (δ := 17/4000000) (ψ := 233983/1000000) 66 19
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t6 : ((430238489293/5000000000000 : ℚ) : ℝ) ≤ stT66 6 := by
  have hc : ((210773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((430238489293/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((210773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c7 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-820099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6330951/10000000) (δ := 367/100000000) (ψ := 233983/1000000) 66 20
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t7 : ((-619974413421/2000000000000 : ℚ) : ℝ) ≤ stT66 7 := by
  have hc : ((-820149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-619974413421/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-820149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c8 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((342783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -381537/1250000) (δ := 213/50000000) (ψ := 233983/1000000) 66 22
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t8 : ((1211743831689/10000000000000 : ℚ) : ℝ) ≤ stT66 8 := by
  have hc : ((342733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1211743831689/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((342733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c9 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((240971/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 336971/5000000) (δ := 61/12500000) (ψ := 233983/1000000) 66 23
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t9 : ((1606389839361/5000000000000 : ℚ) : ℝ) ≤ stT66 9 := by
  have hc : ((481917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1606389839361/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((481917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c10 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((294819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18363/78125) (δ := 599/100000000) (ψ := 233983/1000000) 66 24
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t10 : ((466110142969/2500000000000 : ℚ) : ℝ) ≤ stT66 10 := by
  have hc : ((147397/250000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((466110142969/2500000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((147397/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c11 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((291869/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 59217/250000) (δ := 449/100000000) (ψ := 233983/1000000) 66 25
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t11 : ((219985659593/1250000000000 : ℚ) : ℝ) ≤ stT66 11 := by
  have hc : ((72961/125000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219985659593/1250000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((72961/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c12 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((459149/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 508797/5000000) (δ := 363/100000000) (ψ := 233983/1000000) 66 26
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t12 : ((331344166531/1250000000000 : ℚ) : ℝ) ≤ stT66 12 := by
  have hc : ((114781/125000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((331344166531/1250000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((114781/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c13 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((207271/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -741661/5000000) (δ := 371/100000000) (ψ := 233983/1000000) 66 27
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t13 : ((2299325799/10000000000 : ℚ) : ℝ) ≤ stT66 13 := by
  have hc : ((414517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2299325799/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((414517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c14 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-6294/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -496347/1000000) (δ := 481/100000000) (ψ := 233983/1000000) 66 28
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t14 : ((-538352454429/5000000000000 : ℚ) : ℝ) ≤ stT66 14 := by
  have hc : ((-201433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-538352454429/5000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-201433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c15 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-420017/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3210177/5000000) (δ := 661/100000000) (ψ := 233983/1000000) 66 28
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t15 : ((-542271911769/2500000000000 : ℚ) : ℝ) ≤ stT66 15 := by
  have hc : ((-210021/250000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-542271911769/2500000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-210021/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c16 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((855387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 680623/5000000) (δ := 551/100000000) (ψ := 233983/1000000) 66 29
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t16 : ((855337/4000000 : ℚ) : ℝ) ≤ stT66 16 := by
  have hc : ((855337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((855337/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((855337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c17 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-33179/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2171827/5000000) (δ := 19/5000000) (ψ := 233983/1000000) 66 30
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t17 : ((-80495173473/2000000000000 : ℚ) : ℝ) ≤ stT66 17 := by
  have hc : ((-33189/200000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80495173473/2000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-33189/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c18 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-89541/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1271871/2500000) (δ := 363/100000000) (ψ := 233983/1000000) 66 30
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t18 : ((-211073766673/2000000000000 : ℚ) : ℝ) ≤ stT66 18 := by
  have hc : ((-89551/200000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-211073766673/2000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-89551/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c19 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((777727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -424847/2500000) (δ := 247/50000000) (ψ := 233983/1000000) 66 31
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t19 : ((1784113133289/10000000000000 : ℚ) : ℝ) ≤ stT66 19 := by
  have hc : ((777677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1784113133289/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((777677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c20 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-226613/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3382003/5000000) (δ := 237/50000000) (ψ := 233983/1000000) 66 31
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t20 : ((-253375014267/1250000000000 : ℚ) : ℝ) ≤ stT66 20 := by
  have hc : ((-453251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253375014267/1250000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-453251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c21 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((468399/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -44679/500000) (δ := 419/100000000) (ψ := 233983/1000000) 66 32
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t21 : ((255518859643/1250000000000 : ℚ) : ℝ) ≤ stT66 21 := by
  have hc : ((234187/250000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((255518859643/1250000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((234187/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c22 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-181901/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3391111/5000000) (δ := 339/100000000) (ψ := 233983/1000000) 66 32
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t22 : ((-48479463411/250000000000 : ℚ) : ℝ) ≤ stT66 22 := by
  have hc : ((-181911/200000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48479463411/250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-181911/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c23 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((804193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1989/12500) (δ := 71/12500000) (ψ := 233983/1000000) 66 33
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t23 : ((209594243949/1250000000000 : ℚ) : ℝ) ≤ stT66 23 := by
  have hc : ((804143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209594243949/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((804143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c24 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-56601/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 169723/312500) (δ := 61/12500000) (ψ := 233983/1000000) 66 33
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t24 : ((-28886636163/250000000000 : ℚ) : ℝ) ≤ stT66 24 := by
  have hc : ((-28303/50000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28886636163/250000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-28303/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c25 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((30741/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1770599/5000000) (δ := 517/100000000) (ψ := 233983/1000000) 66 34
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t25 : ((30731/1000000 : ℚ) : ℝ) ≤ stT66 25 := by
  have hc : ((30731/200000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30731/1000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((30731/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c26 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((97057/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 146511/500000) (δ := 417/100000000) (ψ := 233983/1000000) 66 34
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t26 : ((380639777329/5000000000000 : ℚ) : ℝ) ≤ stT66 26 := by
  have hc : ((194089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((380639777329/5000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((194089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c27 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-108393/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6550589/10000000) (δ := 437/100000000) (ψ := 233983/1000000) 66 35
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t27 : ((-834457860097/5000000000000 : ℚ) : ℝ) ≤ stT66 27 := by
  have hc : ((-433597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-834457860097/5000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-433597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c28 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((30497/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -68741/1250000) (δ := 303/50000000) (ψ := 233983/1000000) 66 35
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t28 : ((461047589497/2500000000000 : ℚ) : ℝ) ≤ stT66 28 := by
  have hc : ((487927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((461047589497/2500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((487927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c29 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-250719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 262007/500000) (δ := 233/50000000) (ψ := 233983/1000000) 66 35
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t29 : ((-29101254611/312500000000 : ℚ) : ℝ) ≤ stT66 29 := by
  have hc : ((-31343/62500 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29101254611/312500000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-31343/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c30 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-184917/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1218517/2500000) (δ := 507/100000000) (ψ := 233983/1000000) 66 36
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t30 : ((-84414094241/1250000000000 : ℚ) : ℝ) ≤ stT66 30 := by
  have hc : ((-92471/250000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84414094241/1250000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-92471/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c31 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((977083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 536253/10000000) (δ := 41/6250000) (ψ := 233983/1000000) 66 36
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t31 : ((1754803050749/10000000000000 : ℚ) : ℝ) ≤ stT66 31 := by
  have hc : ((977033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1754803050749/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((977033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c32 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-673637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1443697/2500000) (δ := 169/25000000) (ψ := 233983/1000000) 66 36
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t32 : ((-1190921646929/10000000000000 : ℚ) : ℝ) ≤ stT66 32 := by
  have hc : ((-673687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1190921646929/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-673687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c33 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-72611/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4855851/10000000) (δ := 199/50000000) (ψ := 233983/1000000) 66 37
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t33 : ((-126416966517/2000000000000 : ℚ) : ℝ) ≤ stT66 33 := by
  have hc : ((-72621/200000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126416966517/2000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-72621/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c34 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((999609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 546/78125) (δ := 101/20000000) (ψ := 233983/1000000) 66 37
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t34 : ((342845738323/2000000000000 : ℚ) : ℝ) ≤ stT66 34 := by
  have hc : ((999559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((342845738323/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((999559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c35 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-361929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4852831/10000000) (δ := 189/50000000) (ψ := 233983/1000000) 66 37
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t35 : ((-611856361511/10000000000000 : ℚ) : ℝ) ≤ stT66 35 := by
  have hc : ((-361979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-611856361511/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-361979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c36 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-197679/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6206937/10000000) (δ := 207/50000000) (ψ := 233983/1000000) 66 38
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t36 : ((-658971798461/5000000000000 : ℚ) : ℝ) ≤ stT66 36 := by
  have hc : ((-395383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-658971798461/5000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-395383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c37 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((156211/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1686107/10000000) (δ := 307/50000000) (ψ := 233983/1000000) 66 38
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t37 : ((256792725789/2000000000000 : ℚ) : ℝ) ≤ stT66 37 := by
  have hc : ((156201/200000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((256792725789/2000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((156201/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c38 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((58291/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1357077/5000000) (δ := 369/100000000) (ψ := 233983/1000000) 66 38
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t38 : ((189100674873/2500000000000 : ℚ) : ℝ) ≤ stT66 38 := by
  have hc : ((233139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189100674873/2500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((233139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c39 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-942237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7000109/10000000) (δ := 197/50000000) (ψ := 233983/1000000) 66 38
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t39 : ((-754433605967/5000000000000 : ℚ) : ℝ) ≤ stT66 39 := by
  have hc : ((-942287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-754433605967/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-942287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c40 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-239033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -283151/625000) (δ := 343/100000000) (ψ := 233983/1000000) 66 39
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t40 : ((-378023455537/10000000000000 : ℚ) : ℝ) ≤ stT66 40 := by
  have hc : ((-239083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-378023455537/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-239083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c41 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((983401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -228067/5000000) (δ := 11/2500000) (ψ := 233983/1000000) 66 39
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t41 : ((1535735640687/10000000000000 : ℚ) : ℝ) ≤ stT66 41 := by
  have hc : ((983351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1535735640687/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((983351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c42 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((162093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1759981/5000000) (δ := 543/100000000) (ψ := 233983/1000000) 66 39
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t42 : ((250037696419/10000000000000 : ℚ) : ℝ) ≤ stT66 42 := by
  have hc : ((162043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250037696419/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((162043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c43 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-983737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3701247/5000000) (δ := 563/100000000) (ψ := 233983/1000000) 66 39
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t43 : ((-750130700991/5000000000000 : ℚ) : ℝ) ≤ stT66 43 := by
  have hc : ((-983787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-750130700991/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-983787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c44 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-231951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4512199/10000000) (δ := 453/100000000) (ψ := 233983/1000000) 66 40
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t44 : ((-349754731557/10000000000000 : ℚ) : ℝ) ≤ stT66 44 := by
  have hc : ((-232001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-349754731557/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-232001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c45 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((237177/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -402089/5000000) (δ := 57/10000000) (ψ := 233983/1000000) 66 40
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t45 : ((707087457919/5000000000000 : ℚ) : ℝ) ≤ stT66 45 := by
  have hc : ((474329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((707087457919/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((474329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c46 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((427621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1411171/5000000) (δ := 63/10000000) (ψ := 233983/1000000) 66 40
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t46 : ((630418806249/10000000000000 : ℚ) : ℝ) ≤ stT66 46 := by
  have hc : ((427571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((630418806249/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((427571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c47 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-82913/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3185433/5000000) (δ := 653/100000000) (ψ := 233983/1000000) 66 40
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t47 : ((-1209483407/10000000000 : ℚ) : ℝ) ≤ stT66 47 := by
  have hc : ((-41459/50000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1209483407/10000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-41459/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c48 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-699371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1172657/2000000) (δ := 301/50000000) (ψ := 233983/1000000) 66 41
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t48 : ((-63095467831/625000000000 : ℚ) : ℝ) ≤ stT66 48 := by
  have hc : ((-699421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63095467831/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-699421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c49 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((553329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2461103/10000000) (δ := 621/100000000) (ψ := 233983/1000000) 66 41
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t49 : ((790398334309/10000000000000 : ℚ) : ℝ) ≤ stT66 49 := by
  have hc : ((553279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((790398334309/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((553279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c50 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((117467/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109043/1250000) (δ := 321/50000000) (ψ := 233983/1000000) 66 41
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t50 : ((664458078559/5000000000000 : ℚ) : ℝ) ≤ stT66 50 := by
  have hc : ((469843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((664458078559/5000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((469843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c51 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-21253/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4139777/10000000) (δ := 241/50000000) (ψ := 233983/1000000) 66 41
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t51 : ((-59555351211/5000000000000 : ℚ) : ℝ) ≤ stT66 51 := by
  have hc : ((-42531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59555351211/5000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-42531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c52 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-489623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3671881/5000000) (δ := 271/50000000) (ψ := 233983/1000000) 66 41
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t52 : ((-42438740853/312500000000 : ℚ) : ℝ) ≤ stT66 52 := by
  have hc : ((-30603/31250 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42438740853/312500000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-30603/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c53 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-247443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4177/8000) (δ := 611/100000000) (ψ := 233983/1000000) 66 42
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t53 : ((-42490441201/625000000000 : ℚ) : ℝ) ≤ stT66 53 := by
  have hc : ((-61867/125000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42490441201/625000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-61867/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c54 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((131271/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -267131/1250000) (δ := 391/100000000) (ψ := 233983/1000000) 66 42
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t54 : ((178623512847/2000000000000 : ℚ) : ℝ) ≤ stT66 54 := by
  have hc : ((131261/200000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178623512847/2000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((131261/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c55 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((46861/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2783/31250) (δ := 133/25000000) (ψ := 233983/1000000) 66 42
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t55 : ((126367909083/1000000000000 : ℚ) : ℝ) ≤ stT66 55 := by
  have hc : ((93717/100000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126367909083/1000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((93717/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c56 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((6337/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1931807/5000000) (δ := 37/6250000) (ψ := 233983/1000000) 66 42
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t56 : ((8451467297/2500000000000 : ℚ) : ℝ) ≤ stT66 56 := by
  have hc : ((12649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8451467297/2500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((12649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c57 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-56863/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1696011/2500000) (δ := 27/6250000) (ψ := 233983/1000000) 66 42
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t57 : ((-602568473157/5000000000000 : ℚ) : ℝ) ≤ stT66 57 := by
  have hc : ((-454929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-602568473157/5000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-454929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c58 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-150377/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3027141/5000000) (δ := 621/100000000) (ψ := 233983/1000000) 66 43
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t58 : ((-39493581231/400000000000 : ℚ) : ℝ) ≤ stT66 58 := by
  have hc : ((-150387/200000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39493581231/400000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-150387/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c59 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((10951/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32337/100000) (δ := 381/100000000) (ψ := 233983/1000000) 66 43
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t59 : ((14254382661/400000000000 : ℚ) : ℝ) ≤ stT66 59 := by
  have hc : ((10949/40000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14254382661/400000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((10949/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c60 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((983081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -230263/5000000) (δ := 191/50000000) (ψ := 233983/1000000) 66 43
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t60 : ((634543561407/5000000000000 : ℚ) : ℝ) ≤ stT66 60 := by
  have hc : ((983031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((634543561407/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((983031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c61 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((616329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2266809/10000000) (δ := 201/50000000) (ψ := 233983/1000000) 66 43
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t61 : ((49316494417/625000000000 : ℚ) : ℝ) ≤ stT66 61 := by
  have hc : ((616279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49316494417/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((616279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c62 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-99451/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 989959/2000000) (δ := 271/50000000) (ψ := 233983/1000000) 66 43
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t62 : ((-126318843927/2500000000000 : ℚ) : ℝ) ≤ stT66 62 := by
  have hc : ((-198927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126318843927/2500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-198927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c63 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-124303/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7589851/10000000) (δ := 521/100000000) (ψ := 233983/1000000) 66 43
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t63 : ((-313229973017/2500000000000 : ℚ) : ℝ) ≤ stT66 63 := by
  have hc : ((-497237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-313229973017/2500000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-497237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c64 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-37177/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5519633/10000000) (δ := 533/100000000) (ψ := 233983/1000000) 66 44
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t64 : ((-371801547441/5000000000000 : ℚ) : ℝ) ≤ stT66 64 := by
  have hc : ((-297441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-371801547441/5000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-297441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c65 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((376689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1480721/5000000) (δ := 453/100000000) (ψ := 233983/1000000) 66 44
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t65 : ((467163053733/10000000000000 : ℚ) : ℝ) ≤ stT66 65 := by
  have hc : ((376639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((467163053733/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((376639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c66 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((98439/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -442309/10000000) (δ := 39/10000000) (ψ := 233983/1000000) 66 44
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t66 : ((30290947169/250000000000 : ℚ) : ℝ) ≤ stT66 66 := by
  have hc : ((49217/50000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30290947169/250000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((49217/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c67 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((685449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 101947/500000) (δ := 57/10000000) (ψ := 233983/1000000) 66 44
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t67 : ((418673922953/5000000000000 : ℚ) : ℝ) ≤ stT66 67 := by
  have hc : ((685399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((418673922953/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((685399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c68 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-110371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 448343/1000000) (δ := 63/10000000) (ψ := 233983/1000000) 66 44
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t68 : ((-33468727721/1250000000000 : ℚ) : ℝ) ≤ stT66 68 := by
  have hc : ((-27599/125000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33468727721/1250000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-27599/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c69 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-926911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6892231/10000000) (δ := 67/10000000) (ψ := 233983/1000000) 66 44
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t69 : ((-1115930342499/10000000000000 : ℚ) : ℝ) ≤ stT66 69 := by
  have hc : ((-926961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1115930342499/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-926961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c70 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-211153/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -644159/1000000) (δ := 399/100000000) (ψ := 233983/1000000) 66 45
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t70 : ((-504782258799/5000000000000 : ℚ) : ℝ) ≤ stT66 70 := by
  have hc : ((-422331/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-504782258799/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-422331/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c71 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-69597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32809/80000) (δ := 63/12500000) (ψ := 233983/1000000) 66 45
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t71 : ((-41327902977/5000000000000 : ℚ) : ℝ) ≤ stT66 71 := by
  have hc : ((-69647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41327902977/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-69647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c72 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((150709/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -358679/2000000) (δ := 539/100000000) (ψ := 233983/1000000) 66 45
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t72 : ((177600429189/2000000000000 : ℚ) : ℝ) ≤ stT66 72 := by
  have hc : ((150699/200000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177600429189/2000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((150699/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c73 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((981433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 482503/10000000) (δ := 399/100000000) (ψ := 233983/1000000) 66 45
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t73 : ((1148621458413/10000000000000 : ℚ) : ℝ) ≤ stT66 73 := by
  have hc : ((981383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1148621458413/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((981383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c74 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((230811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 545487/2000000) (δ := 73/12500000) (ψ := 233983/1000000) 66 45
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t74 : ((33535398267/625000000000 : ℚ) : ℝ) ≤ stT66 74 := by
  have hc : ((115393/250000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33535398267/625000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((115393/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c75 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-395027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2471117/5000000) (δ := 579/100000000) (ψ := 233983/1000000) 66 45
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t75 : ((-456195806977/10000000000000 : ℚ) : ℝ) ≤ stT66 75 := by
  have hc : ((-395077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-456195806977/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-395077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c76 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-958097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 445481/625000) (δ := 419/100000000) (ψ := 233983/1000000) 66 45
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t76 : ((-1099070302613/10000000000000 : ℚ) : ℝ) ≤ stT66 76 := by
  have hc : ((-958147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1099070302613/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-958147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c77 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-52543/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3211687/5000000) (δ := 137/25000000) (ψ := 233983/1000000) 66 46
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t77 : ((-239527517307/2500000000000 : ℚ) : ℝ) ≤ stT66 77 := by
  have hc : ((-420369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-239527517307/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-420369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c78 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-183/1250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -536789/1250000) (δ := 127/25000000) (ψ := 233983/1000000) 66 46
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t78 : ((-1658221131/100000000000 : ℚ) : ℝ) ≤ stT66 78 := by
  have hc : ((-2929/20000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1658221131/100000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-2929/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c79 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((1279/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2192373/10000000) (δ := 87/25000000) (ψ := 233983/1000000) 66 46
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t79 : ((14388737643/200000000000 : ℚ) : ℝ) ≤ stT66 79 := by
  have hc : ((12789/20000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14388737643/200000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((12789/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c80 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((998907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58437/5000000) (δ := 117/25000000) (ψ := 233983/1000000) 66 46
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t80 : ((1116755088281/10000000000000 : ℚ) : ℝ) ≤ stT66 80 := by
  have hc : ((998857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1116755088281/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((998857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c81 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((178931/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 966421/5000000) (δ := 67/20000000) (ψ := 233983/1000000) 66 46
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t81 : ((397596626907/5000000000000 : ℚ) : ℝ) ≤ stT66 81 := by
  have hc : ((357837/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((397596626907/5000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((357837/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c82 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-6083/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3957407/10000000) (δ := 97/25000000) (ψ := 233983/1000000) 66 46
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t82 : ((-421572633/312500000000 : ℚ) : ℝ) ≤ stT66 82 := by
  have hc : ((-1527/125000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-421572633/312500000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-1527/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c83 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-362893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 744679/1250000) (δ := 157/25000000) (ψ := 233983/1000000) 66 46
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t83 : ((-199177201137/2500000000000 : ℚ) : ℝ) ≤ stT66 83 := by
  have hc : ((-181459/250000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199177201137/2500000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-181459/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c84 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-499747/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -388723/500000) (δ := 349/50000000) (ψ := 233983/1000000) 66 47
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t84 : ((-13632405787/125000000000 : ℚ) : ℝ) ≤ stT66 84 := by
  have hc : ((-124943/125000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13632405787/125000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-124943/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c85 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-687407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2910887/5000000) (δ := 73/20000000) (ψ := 233983/1000000) 66 47
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t85 : ((-745652297421/10000000000000 : ℚ) : ℝ) ≤ stT66 85 := by
  have hc : ((-687457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-745652297421/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-687457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c86 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((561/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -486491/1250000) (δ := 121/20000000) (ψ := 233983/1000000) 66 47
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t86 : ((602784793/400000000000 : ℚ) : ℝ) ≤ stT66 86 := by
  have hc : ((559/40000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((602784793/400000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((559/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c87 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((175293/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -248049/1250000) (δ := 279/50000000) (ψ := 233983/1000000) 66 47
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t87 : ((23490040927/312500000000 : ℚ) : ℝ) ≤ stT66 87 := by
  have hc : ((350561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23490040927/312500000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((350561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c88 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((999221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -98657/10000000) (δ := 289/50000000) (ψ := 233983/1000000) 66 47
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t88 : ((1065119283513/10000000000000 : ℚ) : ℝ) ≤ stT66 88 := by
  have hc : ((999171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1065119283513/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((999171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c89 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((190191/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1765769/10000000) (δ := 17/4000000) (ψ := 233983/1000000) 66 47
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t89 : ((403177278929/5000000000000 : ℚ) : ℝ) ≤ stT66 89 := by
  have hc : ((380357/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((403177278929/5000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((380357/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c90 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((126709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 902341/2500000) (δ := 89/20000000) (ψ := 233983/1000000) 66 47
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t90 : ((33377559657/2500000000000 : ℚ) : ℝ) ≤ stT66 90 := by
  have hc : ((126659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33377559657/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((126659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c91 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-566489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5432587/10000000) (δ := 137/20000000) (ψ := 233983/1000000) 66 47
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t91 : ((-118778867123/2000000000000 : ℚ) : ℝ) ≤ stT66 91 := by
  have hc : ((-566539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118778867123/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-566539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c92 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-121199/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1808971/2500000) (δ := 101/20000000) (ψ := 233983/1000000) 66 47
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t92 : ((-505461284433/5000000000000 : ℚ) : ℝ) ≤ stT66 92 := by
  have hc : ((-484821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-505461284433/5000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-484821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c93 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-446623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3344139/5000000) (δ := 77/12500000) (ψ := 233983/1000000) 66 48
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t93 : ((-7236758389/78125000000 : ℚ) : ℝ) ≤ stT66 93 := by
  have hc : ((-55831/62500 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7236758389/78125000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-55831/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c94 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-388153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1230889/2500000) (δ := 129/25000000) (ψ := 233983/1000000) 66 48
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t94 : ((-200200557333/5000000000000 : ℚ) : ℝ) ≤ stT66 94 := by
  have hc : ((-388203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-200200557333/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-388203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c95 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((295323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -794377/2500000) (δ := 9/1562500) (ψ := 233983/1000000) 66 48
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t95 : ((151471800997/5000000000000 : ℚ) : ℝ) ≤ stT66 95 := by
  have hc : ((295273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151471800997/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((295273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c96 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((836519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1449743/10000000) (δ := 149/25000000) (ψ := 233983/1000000) 66 48
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t96 : ((42685849539/500000000000 : ℚ) : ℝ) ≤ stT66 96 := by
  have hc : ((836469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42685849539/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((836469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c97 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((31081/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 260117/10000000) (δ := 129/25000000) (ψ := 233983/1000000) 66 48
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t97 : ((252451060383/2500000000000 : ℚ) : ℝ) ≤ stT66 97 := by
  have hc : ((497271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252451060383/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((497271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c98 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((710227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1952439/10000000) (δ := 31/6250000) (ψ := 233983/1000000) 66 48
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t98 : ((89673339613/1250000000000 : ℚ) : ℝ) ≤ stT66 98 := by
  have hc : ((710177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89673339613/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((710177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c99 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((59739/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181379/500000) (δ := 367/100000000) (ψ := 233983/1000000) 66 48
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t99 : ((30007389709/2500000000000 : ℚ) : ℝ) ≤ stT66 99 := by
  have hc : ((29857/250000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30007389709/2500000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((29857/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_c100 :
    |Real.cos (((66 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((233983/1000000 : ℚ) : ℝ))
      - ((-103437/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2642943/5000000) (δ := 139/25000000) (ψ := 233983/1000000) 66 48
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st66_t100 : ((-103447/2000000 : ℚ) : ℝ) ≤ stT66 100 := by
  have hc : ((-103447/200000 : ℚ) : ℝ)
      ≤ Real.cos (((66 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((233983/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st66_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103447/2000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-103447/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st66_p1 : ((972701/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT66 (i+1) := by
  rw [Finset.sum_range_one]
  exact st66_t1

theorem st66_p2 : ((10004924146301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT66 (i+1))
      = (∑ i ∈ Finset.range 1, stT66 (i+1)) + stT66 2 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 1
    simpa using h
  have hprev := st66_p1
  have hstep := st66_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p3 : ((33856357477/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT66 (i+1))
      = (∑ i ∈ Finset.range 2, stT66 (i+1)) + stT66 3 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 2
    simpa using h
  have hprev := st66_p2
  have hstep := st66_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p4 : ((-708066303397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT66 (i+1))
      = (∑ i ∈ Finset.range 3, stT66 (i+1)) + stT66 4 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 3
    simpa using h
  have hprev := st66_p3
  have hstep := st66_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p5 : ((1162774168049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT66 (i+1))
      = (∑ i ∈ Finset.range 4, stT66 (i+1)) + stT66 5 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 4
    simpa using h
  have hprev := st66_p4
  have hstep := st66_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p6 : ((796506328671/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT66 (i+1))
      = (∑ i ∈ Finset.range 5, stT66 (i+1)) + stT66 6 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 5
    simpa using h
  have hprev := st66_p5
  have hstep := st66_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p7 : ((86153247579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT66 (i+1))
      = (∑ i ∈ Finset.range 6, stT66 (i+1)) + stT66 7 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 6
    simpa using h
  have hprev := st66_p6
  have hstep := st66_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p8 : ((324474269817/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT66 (i+1))
      = (∑ i ∈ Finset.range 7, stT66 (i+1)) + stT66 8 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 7
    simpa using h
  have hprev := st66_p7
  have hstep := st66_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p9 : ((451067675799/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT66 (i+1))
      = (∑ i ∈ Finset.range 8, stT66 (i+1)) + stT66 9 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 8
    simpa using h
  have hprev := st66_p8
  have hstep := st66_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p10 : ((3187558664933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT66 (i+1))
      = (∑ i ∈ Finset.range 9, stT66 (i+1)) + stT66 10 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 9
    simpa using h
  have hprev := st66_p9
  have hstep := st66_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p11 : ((813500260661/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT66 (i+1))
      = (∑ i ∈ Finset.range 10, stT66 (i+1)) + stT66 11 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 10
    simpa using h
  have hprev := st66_p10
  have hstep := st66_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p12 : ((5392877969429/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT66 (i+1))
      = (∑ i ∈ Finset.range 11, stT66 (i+1)) + stT66 12 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 11
    simpa using h
  have hprev := st66_p11
  have hstep := st66_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p13 : ((6542540868929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT66 (i+1))
      = (∑ i ∈ Finset.range 12, stT66 (i+1)) + stT66 13 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 12
    simpa using h
  have hprev := st66_p12
  have hstep := st66_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p14 : ((12008376829/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT66 (i+1))
      = (∑ i ∈ Finset.range 13, stT66 (i+1)) + stT66 14 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 13
    simpa using h
  have hprev := st66_p13
  have hstep := st66_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p15 : ((2459822295481/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT66 (i+1))
      = (∑ i ∈ Finset.range 14, stT66 (i+1)) + stT66 15 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 14
    simpa using h
  have hprev := st66_p14
  have hstep := st66_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p16 : ((2994407920481/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT66 (i+1))
      = (∑ i ∈ Finset.range 15, stT66 (i+1)) + stT66 16 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 15
    simpa using h
  have hprev := st66_p15
  have hstep := st66_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p17 : ((11575155814559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT66 (i+1))
      = (∑ i ∈ Finset.range 16, stT66 (i+1)) + stT66 17 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 16
    simpa using h
  have hprev := st66_p16
  have hstep := st66_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p18 : ((5259893490597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT66 (i+1))
      = (∑ i ∈ Finset.range 17, stT66 (i+1)) + stT66 18 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 17
    simpa using h
  have hprev := st66_p17
  have hstep := st66_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p19 : ((12303900114483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT66 (i+1))
      = (∑ i ∈ Finset.range 18, stT66 (i+1)) + stT66 19 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 18
    simpa using h
  have hprev := st66_p18
  have hstep := st66_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p20 : ((10276900000347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT66 (i+1))
      = (∑ i ∈ Finset.range 19, stT66 (i+1)) + stT66 20 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 19
    simpa using h
  have hprev := st66_p19
  have hstep := st66_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p21 : ((12321050877491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT66 (i+1))
      = (∑ i ∈ Finset.range 20, stT66 (i+1)) + stT66 21 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 20
    simpa using h
  have hprev := st66_p20
  have hstep := st66_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p22 : ((10381872341051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT66 (i+1))
      = (∑ i ∈ Finset.range 21, stT66 (i+1)) + stT66 22 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 21
    simpa using h
  have hprev := st66_p21
  have hstep := st66_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p23 : ((12058626292643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT66 (i+1))
      = (∑ i ∈ Finset.range 22, stT66 (i+1)) + stT66 23 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 22
    simpa using h
  have hprev := st66_p22
  have hstep := st66_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p24 : ((10903160846123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT66 (i+1))
      = (∑ i ∈ Finset.range 23, stT66 (i+1)) + stT66 24 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 23
    simpa using h
  have hprev := st66_p23
  have hstep := st66_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p25 : ((11210470846123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT66 (i+1))
      = (∑ i ∈ Finset.range 24, stT66 (i+1)) + stT66 25 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 24
    simpa using h
  have hprev := st66_p24
  have hstep := st66_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p26 : ((11971750400781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT66 (i+1))
      = (∑ i ∈ Finset.range 25, stT66 (i+1)) + stT66 26 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 25
    simpa using h
  have hprev := st66_p25
  have hstep := st66_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p27 : ((10302834680587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT66 (i+1))
      = (∑ i ∈ Finset.range 26, stT66 (i+1)) + stT66 27 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 26
    simpa using h
  have hprev := st66_p26
  have hstep := st66_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p28 : ((485881001543/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT66 (i+1))
      = (∑ i ∈ Finset.range 27, stT66 (i+1)) + stT66 28 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 27
    simpa using h
  have hprev := st66_p27
  have hstep := st66_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p29 : ((11215784891023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT66 (i+1))
      = (∑ i ∈ Finset.range 28, stT66 (i+1)) + stT66 29 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 28
    simpa using h
  have hprev := st66_p28
  have hstep := st66_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p30 : ((2108094427419/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT66 (i+1))
      = (∑ i ∈ Finset.range 29, stT66 (i+1)) + stT66 30 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 29
    simpa using h
  have hprev := st66_p29
  have hstep := st66_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p31 : ((3073818796961/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT66 (i+1))
      = (∑ i ∈ Finset.range 30, stT66 (i+1)) + stT66 31 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 30
    simpa using h
  have hprev := st66_p30
  have hstep := st66_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p32 : ((2220870708183/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT66 (i+1))
      = (∑ i ∈ Finset.range 31, stT66 (i+1)) + stT66 32 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 31
    simpa using h
  have hprev := st66_p31
  have hstep := st66_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p33 : ((1047226870833/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT66 (i+1))
      = (∑ i ∈ Finset.range 32, stT66 (i+1)) + stT66 33 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 32
    simpa using h
  have hprev := st66_p32
  have hstep := st66_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p34 : ((2437299479989/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT66 (i+1))
      = (∑ i ∈ Finset.range 33, stT66 (i+1)) + stT66 34 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 33
    simpa using h
  have hprev := st66_p33
  have hstep := st66_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p35 : ((5787320519217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT66 (i+1))
      = (∑ i ∈ Finset.range 34, stT66 (i+1)) + stT66 35 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 34
    simpa using h
  have hprev := st66_p34
  have hstep := st66_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p36 : ((1282087180189/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT66 (i+1))
      = (∑ i ∈ Finset.range 35, stT66 (i+1)) + stT66 36 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 35
    simpa using h
  have hprev := st66_p35
  have hstep := st66_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p37 : ((11540661070457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT66 (i+1))
      = (∑ i ∈ Finset.range 36, stT66 (i+1)) + stT66 37 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 36
    simpa using h
  have hprev := st66_p36
  have hstep := st66_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p38 : ((12297063769949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT66 (i+1))
      = (∑ i ∈ Finset.range 37, stT66 (i+1)) + stT66 38 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 37
    simpa using h
  have hprev := st66_p37
  have hstep := st66_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p39 : ((2157639311603/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT66 (i+1))
      = (∑ i ∈ Finset.range 38, stT66 (i+1)) + stT66 39 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 38
    simpa using h
  have hprev := st66_p38
  have hstep := st66_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p40 : ((5205086551239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT66 (i+1))
      = (∑ i ∈ Finset.range 39, stT66 (i+1)) + stT66 40 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 39
    simpa using h
  have hprev := st66_p39
  have hstep := st66_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p41 : ((2389181748633/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT66 (i+1))
      = (∑ i ∈ Finset.range 40, stT66 (i+1)) + stT66 41 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 40
    simpa using h
  have hprev := st66_p40
  have hstep := st66_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p42 : ((381123326237/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT66 (i+1))
      = (∑ i ∈ Finset.range 41, stT66 (i+1)) + stT66 42 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 41
    simpa using h
  have hprev := st66_p41
  have hstep := st66_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p43 : ((5347842518801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT66 (i+1))
      = (∑ i ∈ Finset.range 42, stT66 (i+1)) + stT66 43 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 42
    simpa using h
  have hprev := st66_p42
  have hstep := st66_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p44 : ((2069186061209/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT66 (i+1))
      = (∑ i ∈ Finset.range 43, stT66 (i+1)) + stT66 44 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 43
    simpa using h
  have hprev := st66_p43
  have hstep := st66_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p45 : ((11760105221883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT66 (i+1))
      = (∑ i ∈ Finset.range 44, stT66 (i+1)) + stT66 45 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 44
    simpa using h
  have hprev := st66_p44
  have hstep := st66_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p46 : ((3097631007033/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT66 (i+1))
      = (∑ i ∈ Finset.range 45, stT66 (i+1)) + stT66 46 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 45
    simpa using h
  have hprev := st66_p45
  have hstep := st66_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p47 : ((2795260155283/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT66 (i+1))
      = (∑ i ∈ Finset.range 46, stT66 (i+1)) + stT66 47 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 46
    simpa using h
  have hprev := st66_p46
  have hstep := st66_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p48 : ((2542878283959/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT66 (i+1))
      = (∑ i ∈ Finset.range 47, stT66 (i+1)) + stT66 48 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 47
    simpa using h
  have hprev := st66_p47
  have hstep := st66_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p49 : ((2192382294029/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT66 (i+1))
      = (∑ i ∈ Finset.range 48, stT66 (i+1)) + stT66 49 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 48
    simpa using h
  have hprev := st66_p48
  have hstep := st66_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p50 : ((12290827627263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT66 (i+1))
      = (∑ i ∈ Finset.range 49, stT66 (i+1)) + stT66 50 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 49
    simpa using h
  have hprev := st66_p49
  have hstep := st66_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p51 : ((12171716924841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT66 (i+1))
      = (∑ i ∈ Finset.range 50, stT66 (i+1)) + stT66 51 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 50
    simpa using h
  have hprev := st66_p50
  have hstep := st66_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p52 : ((2162735443509/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT66 (i+1))
      = (∑ i ∈ Finset.range 51, stT66 (i+1)) + stT66 52 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 51
    simpa using h
  have hprev := st66_p51
  have hstep := st66_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p53 : ((10133830158329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT66 (i+1))
      = (∑ i ∈ Finset.range 52, stT66 (i+1)) + stT66 53 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 52
    simpa using h
  have hprev := st66_p52
  have hstep := st66_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p54 : ((2756736930641/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT66 (i+1))
      = (∑ i ∈ Finset.range 53, stT66 (i+1)) + stT66 54 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 53
    simpa using h
  have hprev := st66_p53
  have hstep := st66_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p55 : ((6145313406697/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT66 (i+1))
      = (∑ i ∈ Finset.range 54, stT66 (i+1)) + stT66 55 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 54
    simpa using h
  have hprev := st66_p54
  have hstep := st66_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p56 : ((6162216341291/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT66 (i+1))
      = (∑ i ∈ Finset.range 55, stT66 (i+1)) + stT66 56 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 55
    simpa using h
  have hprev := st66_p55
  have hstep := st66_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p57 : ((2779823934067/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT66 (i+1))
      = (∑ i ∈ Finset.range 56, stT66 (i+1)) + stT66 57 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 56
    simpa using h
  have hprev := st66_p56
  have hstep := st66_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p58 : ((10131956205493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT66 (i+1))
      = (∑ i ∈ Finset.range 57, stT66 (i+1)) + stT66 58 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 57
    simpa using h
  have hprev := st66_p57
  have hstep := st66_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p59 : ((5244157886009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT66 (i+1))
      = (∑ i ∈ Finset.range 58, stT66 (i+1)) + stT66 59 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 58
    simpa using h
  have hprev := st66_p58
  have hstep := st66_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p60 : ((734837680927/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT66 (i+1))
      = (∑ i ∈ Finset.range 59, stT66 (i+1)) + stT66 60 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 59
    simpa using h
  have hprev := st66_p59
  have hstep := st66_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p61 : ((49009635959/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT66 (i+1))
      = (∑ i ∈ Finset.range 60, stT66 (i+1)) + stT66 61 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 60
    simpa using h
  have hprev := st66_p60
  have hstep := st66_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p62 : ((3010297857449/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT66 (i+1))
      = (∑ i ∈ Finset.range 61, stT66 (i+1)) + stT66 62 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 61
    simpa using h
  have hprev := st66_p61
  have hstep := st66_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p63 : ((168566742777/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT66 (i+1))
      = (∑ i ∈ Finset.range 62, stT66 (i+1)) + stT66 63 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 62
    simpa using h
  have hprev := st66_p62
  have hstep := st66_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p64 : ((5022334221423/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT66 (i+1))
      = (∑ i ∈ Finset.range 63, stT66 (i+1)) + stT66 64 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 63
    simpa using h
  have hprev := st66_p63
  have hstep := st66_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p65 : ((10511831496579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT66 (i+1))
      = (∑ i ∈ Finset.range 64, stT66 (i+1)) + stT66 65 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 64
    simpa using h
  have hprev := st66_p64
  have hstep := st66_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p66 : ((11723469383339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT66 (i+1))
      = (∑ i ∈ Finset.range 65, stT66 (i+1)) + stT66 66 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 65
    simpa using h
  have hprev := st66_p65
  have hstep := st66_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p67 : ((2512163445849/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT66 (i+1))
      = (∑ i ∈ Finset.range 66, stT66 (i+1)) + stT66 67 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 66
    simpa using h
  have hprev := st66_p66
  have hstep := st66_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p68 : ((12293067407477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT66 (i+1))
      = (∑ i ∈ Finset.range 67, stT66 (i+1)) + stT66 68 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 67
    simpa using h
  have hprev := st66_p67
  have hstep := st66_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p69 : ((5588568532489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT66 (i+1))
      = (∑ i ∈ Finset.range 68, stT66 (i+1)) + stT66 69 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 68
    simpa using h
  have hprev := st66_p68
  have hstep := st66_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p70 : ((508378627369/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT66 (i+1))
      = (∑ i ∈ Finset.range 69, stT66 (i+1)) + stT66 70 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 69
    simpa using h
  have hprev := st66_p69
  have hstep := st66_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p71 : ((5042458370713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT66 (i+1))
      = (∑ i ∈ Finset.range 70, stT66 (i+1)) + stT66 71 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 70
    simpa using h
  have hprev := st66_p70
  have hstep := st66_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p72 : ((10972918887371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT66 (i+1))
      = (∑ i ∈ Finset.range 71, stT66 (i+1)) + stT66 72 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 71
    simpa using h
  have hprev := st66_p71
  have hstep := st66_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p73 : ((1515192543223/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT66 (i+1))
      = (∑ i ∈ Finset.range 72, stT66 (i+1)) + stT66 73 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 72
    simpa using h
  have hprev := st66_p72
  have hstep := st66_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p74 : ((1582263339757/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT66 (i+1))
      = (∑ i ∈ Finset.range 73, stT66 (i+1)) + stT66 74 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 73
    simpa using h
  have hprev := st66_p73
  have hstep := st66_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p75 : ((12201910911079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT66 (i+1))
      = (∑ i ∈ Finset.range 74, stT66 (i+1)) + stT66 75 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 74
    simpa using h
  have hprev := st66_p74
  have hstep := st66_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p76 : ((5551420304233/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT66 (i+1))
      = (∑ i ∈ Finset.range 75, stT66 (i+1)) + stT66 76 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 75
    simpa using h
  have hprev := st66_p75
  have hstep := st66_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p77 : ((5072365269619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT66 (i+1))
      = (∑ i ∈ Finset.range 76, stT66 (i+1)) + stT66 77 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 76
    simpa using h
  have hprev := st66_p76
  have hstep := st66_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p78 : ((4989454213069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT66 (i+1))
      = (∑ i ∈ Finset.range 77, stT66 (i+1)) + stT66 78 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 77
    simpa using h
  have hprev := st66_p77
  have hstep := st66_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p79 : ((83580822721/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT66 (i+1))
      = (∑ i ∈ Finset.range 78, stT66 (i+1)) + stT66 79 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 78
    simpa using h
  have hprev := st66_p78
  have hstep := st66_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p80 : ((11815100396569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT66 (i+1))
      = (∑ i ∈ Finset.range 79, stT66 (i+1)) + stT66 80 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 79
    simpa using h
  have hprev := st66_p79
  have hstep := st66_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p81 : ((12610293650383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT66 (i+1))
      = (∑ i ∈ Finset.range 80, stT66 (i+1)) + stT66 81 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 80
    simpa using h
  have hprev := st66_p80
  have hstep := st66_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p82 : ((12596803326127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT66 (i+1))
      = (∑ i ∈ Finset.range 81, stT66 (i+1)) + stT66 82 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 81
    simpa using h
  have hprev := st66_p81
  have hstep := st66_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p83 : ((11800094521579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT66 (i+1))
      = (∑ i ∈ Finset.range 82, stT66 (i+1)) + stT66 83 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 82
    simpa using h
  have hprev := st66_p82
  have hstep := st66_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p84 : ((10709502058619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT66 (i+1))
      = (∑ i ∈ Finset.range 83, stT66 (i+1)) + stT66 84 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 83
    simpa using h
  have hprev := st66_p83
  have hstep := st66_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p85 : ((4981924880599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT66 (i+1))
      = (∑ i ∈ Finset.range 84, stT66 (i+1)) + stT66 85 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 84
    simpa using h
  have hprev := st66_p84
  have hstep := st66_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p86 : ((9978919381023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT66 (i+1))
      = (∑ i ∈ Finset.range 85, stT66 (i+1)) + stT66 86 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 85
    simpa using h
  have hprev := st66_p85
  have hstep := st66_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p87 : ((10730600690687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT66 (i+1))
      = (∑ i ∈ Finset.range 86, stT66 (i+1)) + stT66 87 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 86
    simpa using h
  have hprev := st66_p86
  have hstep := st66_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p88 : ((58978599871/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT66 (i+1))
      = (∑ i ∈ Finset.range 87, stT66 (i+1)) + stT66 88 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 87
    simpa using h
  have hprev := st66_p87
  have hstep := st66_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p89 : ((6301037266029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT66 (i+1))
      = (∑ i ∈ Finset.range 88, stT66 (i+1)) + stT66 89 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 88
    simpa using h
  have hprev := st66_p88
  have hstep := st66_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p90 : ((6367792385343/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT66 (i+1))
      = (∑ i ∈ Finset.range 89, stT66 (i+1)) + stT66 90 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 89
    simpa using h
  have hprev := st66_p89
  have hstep := st66_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p91 : ((12141690435071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT66 (i+1))
      = (∑ i ∈ Finset.range 90, stT66 (i+1)) + stT66 91 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 90
    simpa using h
  have hprev := st66_p90
  have hstep := st66_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p92 : ((2226153573241/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT66 (i+1))
      = (∑ i ∈ Finset.range 91, stT66 (i+1)) + stT66 92 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 91
    simpa using h
  have hprev := st66_p91
  have hstep := st66_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p93 : ((10204462792413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT66 (i+1))
      = (∑ i ∈ Finset.range 92, stT66 (i+1)) + stT66 93 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 92
    simpa using h
  have hprev := st66_p92
  have hstep := st66_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p94 : ((9804061677747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT66 (i+1))
      = (∑ i ∈ Finset.range 93, stT66 (i+1)) + stT66 94 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 93
    simpa using h
  have hprev := st66_p93
  have hstep := st66_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p95 : ((10107005279741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT66 (i+1))
      = (∑ i ∈ Finset.range 94, stT66 (i+1)) + stT66 95 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 94
    simpa using h
  have hprev := st66_p94
  have hstep := st66_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p96 : ((10960722270521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT66 (i+1))
      = (∑ i ∈ Finset.range 95, stT66 (i+1)) + stT66 96 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 95
    simpa using h
  have hprev := st66_p95
  have hstep := st66_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p97 : ((11970526512053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT66 (i+1))
      = (∑ i ∈ Finset.range 96, stT66 (i+1)) + stT66 97 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 96
    simpa using h
  have hprev := st66_p96
  have hstep := st66_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p98 : ((12687913228957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT66 (i+1))
      = (∑ i ∈ Finset.range 97, stT66 (i+1)) + stT66 98 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 97
    simpa using h
  have hprev := st66_p97
  have hstep := st66_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p99 : ((12807942787793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT66 (i+1))
      = (∑ i ∈ Finset.range 98, stT66 (i+1)) + stT66 99 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 98
    simpa using h
  have hprev := st66_p98
  have hstep := st66_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st66_p100 : ((12290707787793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT66 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT66 (i+1))
      = (∑ i ∈ Finset.range 99, stT66 (i+1)) + stT66 100 := by
    have h := Finset.sum_range_succ (fun i => stT66 (i+1)) 99
    simpa using h
  have hprev := st66_p99
  have hstep := st66_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 66`.** -/
theorem station_66_sign : 0 < hardyG (((66:ℕ)):ℝ) := by
  have hcore := phase_station_lower 66 100 (by norm_num) (by norm_num)
    ((233983/1000000 : ℚ) : ℝ)
  have hchain := st66_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT66 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((66:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((233983/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((66:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((66:ℕ)):ℝ)+1) * ((((66:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((1291129/2200000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((12290707787793/10000000000000 : ℚ) : ℝ) - ((1291129/2200000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((233983/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((66:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((233983/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((66:ℕ)):ℝ))).re
      - Real.sin ((233983/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((66:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((66:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((66:ℕ)):ℝ)
      = ((((66:ℕ)):ℝ) * (Real.log (((66:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((66:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_66
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
  have hθwin : |(((233983/1000000 : ℚ) : ℝ) + ((7:ℤ)) * (2*Real.pi)) - theta (((66:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((66:ℕ)):ℝ))
    (φ := ((233983/1000000 : ℚ) : ℝ) + ((7:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((233983/1000000 : ℚ)) : ℝ) 7).1,
    (cos_sin_shift (((233983/1000000 : ℚ)) : ℝ) 7).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_66_sign
end AxiomAudit
