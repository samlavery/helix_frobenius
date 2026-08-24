import RequestProject.DVPSqrtTable

/-!
# Station `t = 55` of the Hardy ladder (sign +)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT55 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((55 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((87949/250000 : ℚ) : ℝ))

theorem st55_c1 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((187751/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87949/1000000) (δ := 1/100000000) (ψ := 87949/250000) 55 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t1 : ((187741/200000 : ℚ) : ℝ) ≤ stT55 1 := by
  have hc : ((187741/200000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187741/200000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((187741/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c2 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((249349/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45117/2500000) (δ := 57/12500000) (ψ := 87949/250000) 55 6
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t2 : ((3526150194091/5000000000000 : ℚ) : ℝ) ≤ stT55 2 := by
  have hc : ((498673/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3526150194091/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((498673/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c3 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-928063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6899933/10000000) (δ := 489/100000000) (ψ := 87949/250000) 55 10
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t3 : ((-5358463189839/10000000000000 : ℚ) : ℝ) ≤ stT55 3 := by
  have hc : ((-928113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5358463189839/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-928113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c4 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((219853/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49617/400000) (δ := 1/312500) (ψ := 87949/250000) 55 12
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t4 : ((439681/1000000 : ℚ) : ℝ) ≤ stT55 4 := by
  have hc : ((439681/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((439681/1000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((439681/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c5 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((122441/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 506737/10000000) (δ := 491/100000000) (ψ := 87949/250000) 55 14
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t5 : ((438035784553/1000000000000 : ℚ) : ℝ) ≤ stT55 5 := by
  have hc : ((489739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((438035784553/1000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((489739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c6 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-692677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -233599/400000) (δ := 393/100000000) (ψ := 87949/250000) 55 16
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t6 : ((-2828046201141/10000000000000 : ℚ) : ℝ) ≤ stT55 6 := by
  have hc : ((-692727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2828046201141/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-692727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c7 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((247523/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17611/500000) (δ := 279/100000000) (ψ := 87949/250000) 55 17
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t7 : ((467750788131/1250000000000 : ℚ) : ℝ) ≤ stT55 7 := by
  have hc : ((495021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((467750788131/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((495021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c8 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((302849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2300383/10000000) (δ := 329/100000000) (ψ := 87949/250000) 55 18
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t8 : ((133830530649/625000000000 : ℚ) : ℝ) ≤ stT55 8 := by
  have hc : ((37853/62500 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133830530649/625000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((37853/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c9 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((220073/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2787587/10000000) (δ := 83/20000000) (ψ := 87949/250000) 55 19
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t9 : ((45843328749/312500000000 : ℚ) : ℝ) ≤ stT55 9 := by
  have hc : ((13753/31250 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45843328749/312500000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((13753/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c10 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((40499/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 313339/2000000) (δ := 129/25000000) (ψ := 87949/250000) 55 20
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t10 : ((256122301061/1000000000000 : ℚ) : ℝ) ≤ stT55 10 := by
  have hc : ((80993/100000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((256122301061/1000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((80993/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c11 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((915339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1036119/10000000) (δ := 387/100000000) (ψ := 87949/250000) 55 21
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t11 : ((2759699762657/10000000000000 : ℚ) : ℝ) ≤ stT55 11 := by
  have hc : ((915289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2759699762657/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((915289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c12 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-83657/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2390009/5000000) (δ := 37/12500000) (ψ := 87949/250000) 55 22
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t12 : ((-15095818529/156250000000 : ℚ) : ℝ) ≤ stT55 12 := by
  have hc : ((-167339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15095818529/156250000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-167339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c13 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-397663/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1245171/2000000) (δ := 327/100000000) (ψ := 87949/250000) 55 22
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t13 : ((-137873508211/625000000000 : ℚ) : ℝ) ≤ stT55 13 := by
  have hc : ((-49711/62500 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137873508211/625000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-49711/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c14 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((192039/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 353869/5000000) (δ := 3/800000) (ψ := 87949/250000) 55 23
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t14 : ((128304752437/500000000000 : ℚ) : ℝ) ≤ stT55 14 := by
  have hc : ((192029/200000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128304752437/500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((192029/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c15 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-23717/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2756853/5000000) (δ := 277/50000000) (ψ := 87949/250000) 55 24
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t15 : ((-61242197091/400000000000 : ℚ) : ℝ) ≤ stT55 15 := by
  have hc : ((-23719/40000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61242197091/400000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-23719/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c16 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((56181/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3360341/10000000) (δ := 53/12500000) (ψ := 87949/250000) 55 24
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t16 : ((112337/2000000 : ℚ) : ℝ) ≤ stT55 16 := by
  have hc : ((112337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112337/2000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((112337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c17 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-8473/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4011737/10000000) (δ := 157/50000000) (ψ := 87949/250000) 55 25
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t17 : ((-41160733647/5000000000000 : ℚ) : ℝ) ≤ stT55 17 := by
  have hc : ((-16971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41160733647/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-16971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c18 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((31773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 769509/2000000) (δ := 319/100000000) (ψ := 87949/250000) 55 25
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t18 : ((37385904453/5000000000000 : ℚ) : ℝ) ≤ stT55 18 := by
  have hc : ((31723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37385904453/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((31723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c19 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-198349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -177047/400000) (δ := 9/2000000) (ψ := 87949/250000) 55 26
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t19 : ((-227579326521/5000000000000 : ℚ) : ℝ) ≤ stT55 19 := by
  have hc : ((-198399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-227579326521/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-198399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c20 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((496997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2626653/10000000) (δ := 21/5000000) (ψ := 87949/250000) 55 26
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t20 : ((1111206787449/10000000000000 : ℚ) : ℝ) ≤ stT55 20 := by
  have hc : ((496947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1111206787449/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((496947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c21 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-207383/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6372663/10000000) (δ := 171/50000000) (ψ := 87949/250000) 55 27
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t21 : ((-905148209589/5000000000000 : ℚ) : ℝ) ≤ stT55 21 := by
  have hc : ((-414791/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-905148209589/5000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-414791/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c22 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((199991/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23839/10000000) (δ := 291/100000000) (ψ := 87949/250000) 55 27
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t22 : ((426360891867/2000000000000 : ℚ) : ℝ) ≤ stT55 22 := by
  have hc : ((199981/200000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((426360891867/2000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((199981/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c23 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-773019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1533989/2500000) (δ := 241/50000000) (ψ := 87949/250000) 55 27
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t23 : ((-322392192001/2000000000000 : ℚ) : ℝ) ≤ stT55 23 := by
  have hc : ((-773069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-322392192001/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-773069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c24 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((41339/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -186003/500000) (δ := 391/100000000) (ψ := 87949/250000) 55 28
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t24 : ((42165915337/2500000000000 : ℚ) : ℝ) ≤ stT55 24 := by
  have hc : ((20657/250000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42165915337/2500000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((20657/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c25 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((181693/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 473241/2500000) (δ := 431/100000000) (ψ := 87949/250000) 55 28
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t25 : ((363361/2500000 : ℚ) : ℝ) ≤ stT55 25 := by
  have hc : ((363361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((363361/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((363361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c26 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-487143/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1821453/2500000) (δ := 361/100000000) (ψ := 87949/250000) 55 28
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t26 : ((-1866045643/9765625000 : ℚ) : ℝ) ≤ stT55 26 := by
  have hc : ((-15224/15625 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1866045643/9765625000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-15224/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c27 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((2741/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -404107/1250000) (δ := 11/3125000) (ψ := 87949/250000) 55 29
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t27 : ((21096369/400000000 : ℚ) : ℝ) ≤ stT55 27 := by
  have hc : ((5481/20000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21096369/400000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((5481/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c28 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((760263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 353539/2000000) (δ := 511/100000000) (ψ := 87949/250000) 55 29
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t28 : ((718333626043/5000000000000 : ℚ) : ℝ) ≤ stT55 28 := by
  have hc : ((760213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((718333626043/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((760213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c29 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-43771/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 412047/625000) (δ := 381/100000000) (ψ := 87949/250000) 55 29
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t29 : ((-81285375919/500000000000 : ℚ) : ℝ) ≤ stT55 29 := by
  have hc : ((-87547/100000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81285375919/500000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-87547/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c30 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-209147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1113437/2500000) (δ := 453/100000000) (ψ := 87949/250000) 55 30
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t30 : ((-190969874587/5000000000000 : ℚ) : ℝ) ≤ stT55 30 := by
  have hc : ((-209197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190969874587/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-209197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c31 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((999759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 54853/10000000) (δ := 51/10000000) (ψ := 87949/250000) 55 30
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t31 : ((1795530348577/10000000000000 : ℚ) : ℝ) ≤ stT55 31 := by
  have hc : ((999709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1795530348577/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((999709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c32 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-39209/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4420299/10000000) (δ := 13/2500000) (ψ := 87949/250000) 55 30
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t32 : ((-69330053973/2000000000000 : ℚ) : ℝ) ≤ stT55 32 := by
  have hc : ((-39219/200000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69330053973/2000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-39219/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c33 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-23739/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3528281/5000000) (δ := 81/25000000) (ψ := 87949/250000) 55 31
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t33 : ((-165305924697/1000000000000 : ℚ) : ℝ) ≤ stT55 33 := by
  have hc : ((-94961/100000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165305924697/1000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-94961/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c34 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((380267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2951779/10000000) (δ := 409/100000000) (ψ := 87949/250000) 55 31
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t34 : ((130413290349/2000000000000 : ℚ) : ℝ) ≤ stT55 34 := by
  have hc : ((380217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130413290349/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((380217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c35 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((915679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1034007/10000000) (δ := 167/50000000) (ψ := 87949/250000) 55 31
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t35 : ((386923755933/2500000000000 : ℚ) : ℝ) ≤ stT55 35 := by
  have hc : ((915629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((386923755933/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((915629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c36 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-382227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4907503/10000000) (δ := 329/100000000) (ψ := 87949/250000) 55 31
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t36 : ((-637128460759/10000000000000 : ℚ) : ℝ) ≤ stT55 36 := by
  have hc : ((-382277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-637128460759/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-382277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c37 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-37863/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3516551/5000000) (δ := 499/100000000) (ψ := 87949/250000) 55 32
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t37 : ((-1244993627/8000000000 : ℚ) : ℝ) ≤ stT55 37 := by
  have hc : ((-7573/8000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1244993627/8000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-7573/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c38 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((222433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1683109/5000000) (δ := 157/50000000) (ψ := 87949/250000) 55 32
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t38 : ((180376407981/5000000000000 : ℚ) : ℝ) ≤ stT55 38 := by
  have hc : ((222383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180376407981/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((222383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c39 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((498313/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51353/2500000) (δ := 289/100000000) (ψ := 87949/250000) 55 32
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t39 : ((49868694183/312500000000 : ℚ) : ℝ) ≤ stT55 39 := by
  have hc : ((31143/31250 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49868694183/312500000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((31143/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c40 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((24001/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 368661/1000000) (δ := 71/25000000) (ψ := 87949/250000) 55 32
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t40 : ((37929128913/2500000000000 : ℚ) : ℝ) ≤ stT55 40 := by
  have hc : ((47977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37929128913/2500000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((47977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c41 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-476341/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1416369/2000000) (δ := 3/781250) (ψ := 87949/250000) 55 32
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t41 : ((-185989721027/1250000000000 : ℚ) : ℝ) ≤ stT55 41 := by
  have hc : ((-238183/250000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185989721027/1250000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-238183/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c42 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-8224/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1062541/2000000) (δ := 219/50000000) (ψ := 87949/250000) 55 33
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t42 : ((-203057873781/2500000000000 : ℚ) : ℝ) ≤ stT55 42 := by
  have hc : ((-263193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-203057873781/2500000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-263193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c43 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((21069/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1038631/5000000) (δ := 117/25000000) (ψ := 87949/250000) 55 33
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t43 : ((102808083763/1000000000000 : ℚ) : ℝ) ≤ stT55 43 := by
  have hc : ((337079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102808083763/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((337079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c44 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((907493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1083797/10000000) (δ := 179/50000000) (ψ := 87949/250000) 55 33
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t44 : ((342005284827/2500000000000 : ℚ) : ℝ) ≤ stT55 44 := by
  have hc : ((907443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((342005284827/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((907443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c45 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-98569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 834763/2000000) (δ := 103/20000000) (ψ := 87949/250000) 55 33
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t45 : ((-18376565841/1250000000000 : ℚ) : ℝ) ≤ stT55 45 := by
  have hc : ((-98619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18376565841/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-98619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c46 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-193111/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3597957/5000000) (δ := 21/4000000) (ψ := 87949/250000) 55 33
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t46 : ((-14237073241/100000000000 : ℚ) : ℝ) ≤ stT55 46 := by
  have hc : ((-193121/200000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14237073241/100000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-193121/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c47 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-606127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2777473/5000000) (δ := 547/100000000) (ψ := 87949/250000) 55 34
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t47 : ((-17684001621/200000000000 : ℚ) : ℝ) ≤ stT55 47 := by
  have hc : ((-606177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17684001621/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-606177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c48 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((485343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1330051/5000000) (δ := 487/100000000) (ψ := 87949/250000) 55 34
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t48 : ((5603678271/80000000000 : ℚ) : ℝ) ≤ stT55 48 := by
  have hc : ((485293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5603678271/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((485293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c49 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((19951/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3501/200000) (δ := 273/50000000) (ψ := 87949/250000) 55 34
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t49 : ((569999829/4000000000 : ℚ) : ℝ) ≤ stT55 49 := by
  have hc : ((399/400 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((569999829/4000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((399/400 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c50 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((94961/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1476461/5000000) (δ := 527/100000000) (ψ := 87949/250000) 55 34
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t50 : ((268554806061/5000000000000 : ℚ) : ℝ) ≤ stT55 50 := by
  have hc : ((189897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268554806061/5000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((189897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c51 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-80481/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5675783/10000000) (δ := 387/100000000) (ψ := 87949/250000) 55 34
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t51 : ((-450819067669/5000000000000 : ℚ) : ℝ) ≤ stT55 51 := by
  have hc : ((-321949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-450819067669/5000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-321949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c52 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-490357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7362193/10000000) (δ := 223/50000000) (ψ := 87949/250000) 55 35
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t52 : ((-340018864441/2500000000000 : ℚ) : ℝ) ≤ stT55 52 := by
  have hc : ((-245191/250000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-340018864441/2500000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-245191/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c53 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-40083/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2371533/5000000) (δ := 233/50000000) (ψ := 87949/250000) 55 35
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t53 : ((-110133668671/2500000000000 : ℚ) : ℝ) ≤ stT55 53 := by
  have hc : ((-160357/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110133668671/2500000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-160357/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c54 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((645469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1086449/5000000) (δ := 37/12500000) (ψ := 87949/250000) 55 35
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t54 : ((878303601513/10000000000000 : ℚ) : ℝ) ≤ stT55 54 := by
  have hc : ((645419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((878303601513/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((645419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c55 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((99021/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 350109/10000000) (δ := 487/100000000) (ψ := 87949/250000) 55 35
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t55 : ((16689134423/125000000000 : ℚ) : ℝ) ≤ stT55 55 := by
  have hc : ((12377/12500 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16689134423/125000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((12377/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c56 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((4257/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2827653/10000000) (δ := 497/100000000) (ψ := 87949/250000) 55 35
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t56 : ((5687986489/100000000000 : ℚ) : ℝ) ≤ stT55 56 := by
  have hc : ((8513/20000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5687986489/100000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((8513/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c57 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-254379/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1052269/2000000) (δ := 377/100000000) (ψ := 87949/250000) 55 35
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t57 : ((-84241623333/1250000000000 : ℚ) : ℝ) ≤ stT55 57 := by
  have hc : ((-63601/125000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84241623333/1250000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-63601/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c58 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-996761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 765271/1000000) (δ := 119/25000000) (ψ := 87949/250000) 55 35
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t58 : ((-261775527143/2000000000000 : ℚ) : ℝ) ≤ stT55 58 := by
  have hc : ((-996811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-261775527143/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-996811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c59 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-163169/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5704769/10000000) (δ := 153/50000000) (ψ := 87949/250000) 55 36
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t59 : ((-42488872607/500000000000 : ℚ) : ℝ) ≤ stT55 59 := by
  have hc : ((-326363/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42488872607/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-326363/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c60 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((211667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -339379/1000000) (δ := 357/100000000) (ψ := 87949/250000) 55 36
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t60 : ((136598138649/5000000000000 : ℚ) : ℝ) ≤ stT55 60 := by
  have hc : ((211617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136598138649/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((211617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c61 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((45057/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1121011/10000000) (δ := 367/100000000) (ψ := 87949/250000) 55 36
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t61 : ((7210792507/62500000000 : ℚ) : ℝ) ≤ stT55 61 := by
  have hc : ((90109/100000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7210792507/62500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((90109/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c62 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((902213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 111481/1000000) (δ := 457/100000000) (ψ := 87949/250000) 55 36
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t62 : ((1145747912163/10000000000000 : ℚ) : ℝ) ≤ stT55 62 := by
  have hc : ((902163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1145747912163/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((902163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c63 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((121207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3314857/10000000) (δ := 13/3125000) (ψ := 87949/250000) 55 36
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t63 : ((76337449671/2500000000000 : ℚ) : ℝ) ≤ stT55 63 := by
  have hc : ((60591/250000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76337449671/2500000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((60591/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c64 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-291049/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 85629/156250) (δ := 447/100000000) (ψ := 87949/250000) 55 36
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t64 : ((-181921395537/2500000000000 : ℚ) : ℝ) ≤ stT55 64 := by
  have hc : ((-145537/250000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181921395537/2500000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-145537/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c65 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-497661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3806041/5000000) (δ := 387/100000000) (ψ := 87949/250000) 55 36
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t65 : ((-77162979341/625000000000 : ℚ) : ℝ) ≤ stT55 65 := by
  have hc : ((-248843/250000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77162979341/625000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-248843/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c66 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-29459/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1499151/2500000) (δ := 13/4000000) (ψ := 87949/250000) 55 37
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t66 : ((-7252797363/80000000000 : ℚ) : ℝ) ≤ stT55 66 := by
  have hc : ((-29461/40000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7252797363/80000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-29461/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c67 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-381/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -61389/156250) (δ := 91/20000000) (ψ := 87949/250000) 55 37
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t67 : ((-49600817/500000000000 : ℚ) : ℝ) ≤ stT55 67 := by
  have hc : ((-203/250000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49600817/500000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-203/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c68 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((363543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1891821/10000000) (δ := 101/20000000) (ψ := 87949/250000) 55 37
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t68 : ((110207570301/1250000000000 : ℚ) : ℝ) ≤ stT55 68 := by
  have hc : ((181759/250000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110207570301/1250000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((181759/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c69 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((998933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 115513/10000000) (δ := 109/20000000) (ψ := 87949/250000) 55 37
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t69 : ((601256645307/5000000000000 : ℚ) : ℝ) ≤ stT55 69 := by
  have hc : ((998883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((601256645307/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((998883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c70 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((334629/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 418793/2000000) (δ := 63/20000000) (ψ := 87949/250000) 55 37
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t70 : ((24995504357/312500000000 : ℚ) : ℝ) ≤ stT55 70 := by
  have hc : ((83651/125000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24995504357/312500000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((83651/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c71 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-46927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 63193/156250) (δ := 209/50000000) (ψ := 87949/250000) 55 37
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t71 : ((-27875729007/5000000000000 : ℚ) : ℝ) ≤ stT55 71 := by
  have hc : ((-46977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27875729007/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-46977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c72 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-36427/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 298373/500000) (δ := 93/20000000) (ψ := 87949/250000) 55 37
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t72 : ((-5366575363/62500000000 : ℚ) : ℝ) ≤ stT55 72 := by
  have hc : ((-72859/100000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5366575363/62500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-72859/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c73 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-124999/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7843921/10000000) (δ := 81/25000000) (ψ := 87949/250000) 55 38
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t73 : ((-146307644663/1250000000000 : ℚ) : ℝ) ≤ stT55 73 := by
  have hc : ((-500021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146307644663/1250000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-500021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c74 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-146019/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -746643/1250000) (δ := 509/100000000) (ψ := 87949/250000) 55 38
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t74 : ((-169755353833/2000000000000 : ℚ) : ℝ) ≤ stT55 74 := by
  have hc : ((-146029/200000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169755353833/2000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-146029/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c75 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-80109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4127479/10000000) (δ := 247/50000000) (ψ := 87949/250000) 55 38
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t75 : ((-92559677459/10000000000000 : ℚ) : ℝ) ≤ stT55 75 := by
  have hc : ((-80159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92559677459/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-80159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c76 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((301913/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115313/500000) (δ := 167/50000000) (ψ := 87949/250000) 55 38
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t76 : ((2705383463/39062500000 : ℚ) : ℝ) ≤ stT55 76 := by
  have hc : ((9434/15625 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2705383463/39062500000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((9434/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c77 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((979357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -508849/10000000) (δ := 111/25000000) (ψ := 87949/250000) 55 38
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t77 : ((223204630747/2000000000000 : ℚ) : ℝ) ≤ stT55 77 := by
  have hc : ((979307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((223204630747/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((979307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c78 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((874619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1265369/10000000) (δ := 53/12500000) (ψ := 87949/250000) 55 38
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t78 : ((990254363613/10000000000000 : ℚ) : ℝ) ≤ stT55 78 := by
  have hc : ((874569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((990254363613/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((874569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c79 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((356017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1508493/5000000) (δ := 309/100000000) (ψ := 87949/250000) 55 38
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t79 : ((400493844129/10000000000000 : ℚ) : ℝ) ≤ stT55 79 := by
  have hc : ((355967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((400493844129/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((355967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c80 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-32199/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 593321/1250000) (δ := 91/25000000) (ψ := 87949/250000) 55 38
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t80 : ((-4500645867/125000000000 : ℚ) : ℝ) ≤ stT55 80 := by
  have hc : ((-8051/25000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4500645867/125000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-8051/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c81 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-4237/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1290933/2000000) (δ := 319/100000000) (ψ := 87949/250000) 55 38
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t81 : ((-2354029661/25000000000 : ℚ) : ℝ) ≤ stT55 81 := by
  have hc : ((-16949/20000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2354029661/25000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-16949/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c82 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-49669/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7566161/10000000) (δ := 293/100000000) (ψ := 87949/250000) 55 39
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t82 : ((-27426516097/250000000000 : ℚ) : ℝ) ≤ stT55 82 := by
  have hc : ((-99343/100000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27426516097/250000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-99343/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c83 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-177411/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2949737/5000000) (δ := 513/100000000) (ψ := 87949/250000) 55 39
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t83 : ((-389495325621/5000000000000 : ℚ) : ℝ) ≤ stT55 83 := by
  have hc : ((-354847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-389495325621/5000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-354847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c84 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-64967/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1063187/2500000) (δ := 573/100000000) (ψ := 87949/250000) 55 39
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t84 : ((-221600379/15625000000 : ℚ) : ℝ) ≤ stT55 84 := by
  have hc : ((-2031/15625 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221600379/15625000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-2031/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c85 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((248697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -262551/1000000) (δ := 3/1000000) (ψ := 87949/250000) 55 39
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t85 : ((2107207673/39062500000 : ℚ) : ℝ) ≤ stT55 85 := by
  have hc : ((7771/15625 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2107207673/39062500000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((7771/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c86 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((114793/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -127163/1250000) (δ := 27/5000000) (ψ := 87949/250000) 55 39
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t86 : ((495110607069/5000000000000 : ℚ) : ℝ) ≤ stT55 86 := by
  have hc : ((459147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((495110607069/5000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((459147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c87 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((973911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 572309/10000000) (δ := 443/100000000) (ψ := 87949/250000) 55 39
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t87 : ((65255504027/625000000000 : ℚ) : ℝ) ≤ stT55 87 := by
  have hc : ((973861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65255504027/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((973861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c88 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((654329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 428751/2000000) (δ := 453/100000000) (ψ := 87949/250000) 55 39
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t88 : ((697463376837/10000000000000 : ℚ) : ℝ) ≤ stT55 88 := by
  have hc : ((654279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((697463376837/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((654279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c89 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((9169/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3697443/10000000) (δ := 37/10000000) (ψ := 87949/250000) 55 39
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t89 : ((2428453127/250000000000 : ℚ) : ℝ) ≤ stT55 89 := by
  have hc : ((2291/25000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2428453127/250000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((2291/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c90 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-15601/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1308443/2500000) (δ := 19/5000000) (ψ := 87949/250000) 55 39
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t90 : ((-263144830613/5000000000000 : ℚ) : ℝ) ≤ stT55 90 := by
  have hc : ((-249641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-263144830613/5000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-249641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c91 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-452303/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2161/3200) (δ := 3/500000) (ψ := 87949/250000) 55 39
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t91 : ((-11854216437/125000000000 : ℚ) : ℝ) ≤ stT55 91 := by
  have hc : ((-56541/62500 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11854216437/125000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-56541/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c92 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-987107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7452091/10000000) (δ := 11/2500000) (ψ := 87949/250000) 55 40
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t92 : ((-1029183234961/10000000000000 : ℚ) : ℝ) ≤ stT55 92 := by
  have hc : ((-987157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1029183234961/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-987157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c93 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-728027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -596559/1000000) (δ := 53/10000000) (ψ := 87949/250000) 55 40
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t93 : ((-94372612663/1250000000000 : ℚ) : ℝ) ≤ stT55 93 := by
  have hc : ((-728077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94372612663/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-728077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c94 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-225249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1123747/2500000) (δ := 23/5000000) (ψ := 87949/250000) 55 40
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t94 : ((-116189172589/5000000000000 : ℚ) : ℝ) ≤ stT55 94 := by
  have hc : ((-225299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116189172589/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-225299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c95 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((347419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -759987/2500000) (δ := 51/10000000) (ψ := 87949/250000) 55 40
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t95 : ((178196475941/5000000000000 : ℚ) : ℝ) ≤ stT55 95 := by
  have hc : ((347369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178196475941/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((347369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c96 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((802061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -100009/625000) (δ := 13/2500000) (ψ := 87949/250000) 55 40
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t96 : ((40927423341/500000000000 : ℚ) : ℝ) ≤ stT55 96 := by
  have hc : ((802011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40927423341/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((802011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c97 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((124693/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -175261/10000000) (δ := 11/2500000) (ψ := 87949/250000) 55 40
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t97 : ((253200385731/2500000000000 : ℚ) : ℝ) ≤ stT55 97 := by
  have hc : ((498747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((253200385731/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((498747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c98 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((440221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19297/156250) (δ := 9/2000000) (ψ := 87949/250000) 55 40
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t98 : ((13895777181/156250000000 : ℚ) : ℝ) ≤ stT55 98 := by
  have hc : ((110049/125000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13895777181/156250000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((110049/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c99 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((247751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2630959/10000000) (δ := 29/10000000) (ψ := 87949/250000) 55 40
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t99 : ((124486897931/2500000000000 : ℚ) : ℝ) ≤ stT55 99 := by
  have hc : ((123863/250000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124486897931/2500000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((123863/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_c100 :
    |Real.cos (((55 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((87949/250000 : ℚ) : ℝ))
      - ((-34349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50161/125000) (δ := 3/625000) (ψ := 87949/250000) 55 40
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st55_t100 : ((-34399/10000000 : ℚ) : ℝ) ≤ stT55 100 := by
  have hc : ((-34399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((55 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((87949/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st55_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34399/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-34399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st55_p1 : ((187741/200000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT55 (i+1) := by
  rw [Finset.sum_range_one]
  exact st55_t1

theorem st55_p2 : ((8219675194091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT55 (i+1))
      = (∑ i ∈ Finset.range 1, stT55 (i+1)) + stT55 2 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 1
    simpa using h
  have hprev := st55_p1
  have hstep := st55_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p3 : ((11080887198343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT55 (i+1))
      = (∑ i ∈ Finset.range 2, stT55 (i+1)) + stT55 3 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 2
    simpa using h
  have hprev := st55_p2
  have hstep := st55_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p4 : ((15477697198343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT55 (i+1))
      = (∑ i ∈ Finset.range 3, stT55 (i+1)) + stT55 4 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 3
    simpa using h
  have hprev := st55_p3
  have hstep := st55_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p5 : ((19858055043873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT55 (i+1))
      = (∑ i ∈ Finset.range 4, stT55 (i+1)) + stT55 5 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 4
    simpa using h
  have hprev := st55_p4
  have hstep := st55_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p6 : ((4257502210683/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT55 (i+1))
      = (∑ i ∈ Finset.range 5, stT55 (i+1)) + stT55 6 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 5
    simpa using h
  have hprev := st55_p5
  have hstep := st55_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p7 : ((1038600757389/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT55 (i+1))
      = (∑ i ∈ Finset.range 6, stT55 (i+1)) + stT55 7 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 6
    simpa using h
  have hprev := st55_p6
  have hstep := st55_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p8 : ((5728325909541/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT55 (i+1))
      = (∑ i ∈ Finset.range 7, stT55 (i+1)) + stT55 8 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 7
    simpa using h
  have hprev := st55_p7
  have hstep := st55_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p9 : ((6095072539533/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT55 (i+1))
      = (∑ i ∈ Finset.range 8, stT55 (i+1)) + stT55 9 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 8
    simpa using h
  have hprev := st55_p8
  have hstep := st55_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p10 : ((13470756584371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT55 (i+1))
      = (∑ i ∈ Finset.range 9, stT55 (i+1)) + stT55 10 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 9
    simpa using h
  have hprev := st55_p9
  have hstep := st55_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p11 : ((29701212931399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT55 (i+1))
      = (∑ i ∈ Finset.range 10, stT55 (i+1)) + stT55 11 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 10
    simpa using h
  have hprev := st55_p10
  have hstep := st55_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p12 : ((28735080545543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT55 (i+1))
      = (∑ i ∈ Finset.range 11, stT55 (i+1)) + stT55 12 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 11
    simpa using h
  have hprev := st55_p11
  have hstep := st55_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p13 : ((26529104414167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT55 (i+1))
      = (∑ i ∈ Finset.range 12, stT55 (i+1)) + stT55 13 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 12
    simpa using h
  have hprev := st55_p12
  have hstep := st55_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p14 : ((29095199462907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT55 (i+1))
      = (∑ i ∈ Finset.range 13, stT55 (i+1)) + stT55 14 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 13
    simpa using h
  have hprev := st55_p13
  have hstep := st55_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p15 : ((1722759033477/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT55 (i+1))
      = (∑ i ∈ Finset.range 14, stT55 (i+1)) + stT55 15 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 14
    simpa using h
  have hprev := st55_p14
  have hstep := st55_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p16 : ((1757864345977/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT55 (i+1))
      = (∑ i ∈ Finset.range 15, stT55 (i+1)) + stT55 16 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 15
    simpa using h
  have hprev := st55_p15
  have hstep := st55_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p17 : ((14021754034169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT55 (i+1))
      = (∑ i ∈ Finset.range 16, stT55 (i+1)) + stT55 17 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 16
    simpa using h
  have hprev := st55_p16
  have hstep := st55_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p18 : ((7029569969311/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT55 (i+1))
      = (∑ i ∈ Finset.range 17, stT55 (i+1)) + stT55 18 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 17
    simpa using h
  have hprev := st55_p17
  have hstep := st55_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p19 : ((13831560612101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT55 (i+1))
      = (∑ i ∈ Finset.range 18, stT55 (i+1)) + stT55 19 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 18
    simpa using h
  have hprev := st55_p18
  have hstep := st55_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p20 : ((28774328011651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT55 (i+1))
      = (∑ i ∈ Finset.range 19, stT55 (i+1)) + stT55 20 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 19
    simpa using h
  have hprev := st55_p19
  have hstep := st55_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p21 : ((26964031592473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT55 (i+1))
      = (∑ i ∈ Finset.range 20, stT55 (i+1)) + stT55 21 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 20
    simpa using h
  have hprev := st55_p20
  have hstep := st55_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p22 : ((909244876619/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT55 (i+1))
      = (∑ i ∈ Finset.range 21, stT55 (i+1)) + stT55 22 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 21
    simpa using h
  have hprev := st55_p21
  have hstep := st55_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p23 : ((27483875091803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT55 (i+1))
      = (∑ i ∈ Finset.range 22, stT55 (i+1)) + stT55 23 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 22
    simpa using h
  have hprev := st55_p22
  have hstep := st55_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p24 : ((27652538753151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT55 (i+1))
      = (∑ i ∈ Finset.range 23, stT55 (i+1)) + stT55 24 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 23
    simpa using h
  have hprev := st55_p23
  have hstep := st55_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p25 : ((29105982753151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT55 (i+1))
      = (∑ i ∈ Finset.range 24, stT55 (i+1)) + stT55 25 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 24
    simpa using h
  have hprev := st55_p24
  have hstep := st55_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p26 : ((27195152014719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT55 (i+1))
      = (∑ i ∈ Finset.range 25, stT55 (i+1)) + stT55 26 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 25
    simpa using h
  have hprev := st55_p25
  have hstep := st55_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p27 : ((27722561239719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT55 (i+1))
      = (∑ i ∈ Finset.range 26, stT55 (i+1)) + stT55 27 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 26
    simpa using h
  have hprev := st55_p26
  have hstep := st55_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p28 : ((5831845698361/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT55 (i+1))
      = (∑ i ∈ Finset.range 27, stT55 (i+1)) + stT55 28 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 27
    simpa using h
  have hprev := st55_p27
  have hstep := st55_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p29 : ((1101340838937/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT55 (i+1))
      = (∑ i ∈ Finset.range 28, stT55 (i+1)) + stT55 29 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 28
    simpa using h
  have hprev := st55_p28
  have hstep := st55_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p30 : ((27151581224251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT55 (i+1))
      = (∑ i ∈ Finset.range 29, stT55 (i+1)) + stT55 30 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 29
    simpa using h
  have hprev := st55_p29
  have hstep := st55_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p31 : ((7236777893207/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT55 (i+1))
      = (∑ i ∈ Finset.range 30, stT55 (i+1)) + stT55 31 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 30
    simpa using h
  have hprev := st55_p30
  have hstep := st55_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p32 : ((28600461302963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT55 (i+1))
      = (∑ i ∈ Finset.range 31, stT55 (i+1)) + stT55 32 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 31
    simpa using h
  have hprev := st55_p31
  have hstep := st55_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p33 : ((26947402055993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT55 (i+1))
      = (∑ i ∈ Finset.range 32, stT55 (i+1)) + stT55 33 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 32
    simpa using h
  have hprev := st55_p32
  have hstep := st55_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p34 : ((13799734253869/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT55 (i+1))
      = (∑ i ∈ Finset.range 33, stT55 (i+1)) + stT55 34 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 33
    simpa using h
  have hprev := st55_p33
  have hstep := st55_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p35 : ((2914716353147/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT55 (i+1))
      = (∑ i ∈ Finset.range 34, stT55 (i+1)) + stT55 35 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 34
    simpa using h
  have hprev := st55_p34
  have hstep := st55_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p36 : ((28510035070711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT55 (i+1))
      = (∑ i ∈ Finset.range 35, stT55 (i+1)) + stT55 36 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 35
    simpa using h
  have hprev := st55_p35
  have hstep := st55_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p37 : ((26953793036961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT55 (i+1))
      = (∑ i ∈ Finset.range 36, stT55 (i+1)) + stT55 37 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 36
    simpa using h
  have hprev := st55_p36
  have hstep := st55_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p38 : ((27314545852923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT55 (i+1))
      = (∑ i ∈ Finset.range 37, stT55 (i+1)) + stT55 38 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 37
    simpa using h
  have hprev := st55_p37
  have hstep := st55_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p39 : ((28910344066779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT55 (i+1))
      = (∑ i ∈ Finset.range 38, stT55 (i+1)) + stT55 39 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 38
    simpa using h
  have hprev := st55_p38
  have hstep := st55_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p40 : ((29062060582431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT55 (i+1))
      = (∑ i ∈ Finset.range 39, stT55 (i+1)) + stT55 40 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 39
    simpa using h
  have hprev := st55_p39
  have hstep := st55_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p41 : ((5514828562843/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT55 (i+1))
      = (∑ i ∈ Finset.range 40, stT55 (i+1)) + stT55 41 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 40
    simpa using h
  have hprev := st55_p40
  have hstep := st55_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p42 : ((26761911319091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT55 (i+1))
      = (∑ i ∈ Finset.range 41, stT55 (i+1)) + stT55 42 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 41
    simpa using h
  have hprev := st55_p41
  have hstep := st55_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p43 : ((27789992156721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT55 (i+1))
      = (∑ i ∈ Finset.range 42, stT55 (i+1)) + stT55 43 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 42
    simpa using h
  have hprev := st55_p42
  have hstep := st55_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p44 : ((29158013296029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT55 (i+1))
      = (∑ i ∈ Finset.range 43, stT55 (i+1)) + stT55 44 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 43
    simpa using h
  have hprev := st55_p43
  have hstep := st55_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p45 : ((29011000769301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT55 (i+1))
      = (∑ i ∈ Finset.range 44, stT55 (i+1)) + stT55 45 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 44
    simpa using h
  have hprev := st55_p44
  have hstep := st55_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p46 : ((27587293445201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT55 (i+1))
      = (∑ i ∈ Finset.range 45, stT55 (i+1)) + stT55 46 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 45
    simpa using h
  have hprev := st55_p45
  have hstep := st55_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p47 : ((26703093364151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT55 (i+1))
      = (∑ i ∈ Finset.range 46, stT55 (i+1)) + stT55 47 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 46
    simpa using h
  have hprev := st55_p46
  have hstep := st55_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p48 : ((13701776574013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT55 (i+1))
      = (∑ i ∈ Finset.range 47, stT55 (i+1)) + stT55 48 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 47
    simpa using h
  have hprev := st55_p47
  have hstep := st55_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p49 : ((14414276360263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT55 (i+1))
      = (∑ i ∈ Finset.range 48, stT55 (i+1)) + stT55 49 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 48
    simpa using h
  have hprev := st55_p48
  have hstep := st55_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p50 : ((3670707791581/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT55 (i+1))
      = (∑ i ∈ Finset.range 49, stT55 (i+1)) + stT55 50 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 49
    simpa using h
  have hprev := st55_p49
  have hstep := st55_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p51 : ((2846402419731/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT55 (i+1))
      = (∑ i ∈ Finset.range 50, stT55 (i+1)) + stT55 51 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 50
    simpa using h
  have hprev := st55_p50
  have hstep := st55_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p52 : ((13551974369773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT55 (i+1))
      = (∑ i ∈ Finset.range 51, stT55 (i+1)) + stT55 52 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 51
    simpa using h
  have hprev := st55_p51
  have hstep := st55_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p53 : ((13331707032431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT55 (i+1))
      = (∑ i ∈ Finset.range 52, stT55 (i+1)) + stT55 53 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 52
    simpa using h
  have hprev := st55_p52
  have hstep := st55_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p54 : ((220333741331/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT55 (i+1))
      = (∑ i ∈ Finset.range 53, stT55 (i+1)) + stT55 54 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 53
    simpa using h
  have hprev := st55_p53
  have hstep := st55_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p55 : ((5775369684043/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT55 (i+1))
      = (∑ i ∈ Finset.range 54, stT55 (i+1)) + stT55 55 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 54
    simpa using h
  have hprev := st55_p54
  have hstep := st55_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p56 : ((5889129413823/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT55 (i+1))
      = (∑ i ∈ Finset.range 55, stT55 (i+1)) + stT55 56 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 55
    simpa using h
  have hprev := st55_p55
  have hstep := st55_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p57 : ((28771714082451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT55 (i+1))
      = (∑ i ∈ Finset.range 56, stT55 (i+1)) + stT55 57 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 56
    simpa using h
  have hprev := st55_p56
  have hstep := st55_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p58 : ((1716427277921/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT55 (i+1))
      = (∑ i ∈ Finset.range 57, stT55 (i+1)) + stT55 58 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 57
    simpa using h
  have hprev := st55_p57
  have hstep := st55_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p59 : ((6653264748649/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT55 (i+1))
      = (∑ i ∈ Finset.range 58, stT55 (i+1)) + stT55 59 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 58
    simpa using h
  have hprev := st55_p58
  have hstep := st55_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p60 : ((13443127635947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT55 (i+1))
      = (∑ i ∈ Finset.range 59, stT55 (i+1)) + stT55 60 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 59
    simpa using h
  have hprev := st55_p59
  have hstep := st55_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p61 : ((14019991036507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT55 (i+1))
      = (∑ i ∈ Finset.range 60, stT55 (i+1)) + stT55 61 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 60
    simpa using h
  have hprev := st55_p60
  have hstep := st55_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p62 : ((29185729985177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT55 (i+1))
      = (∑ i ∈ Finset.range 61, stT55 (i+1)) + stT55 62 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 61
    simpa using h
  have hprev := st55_p61
  have hstep := st55_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p63 : ((29491079783861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT55 (i+1))
      = (∑ i ∈ Finset.range 62, stT55 (i+1)) + stT55 63 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 62
    simpa using h
  have hprev := st55_p62
  have hstep := st55_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p64 : ((28763394201713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT55 (i+1))
      = (∑ i ∈ Finset.range 63, stT55 (i+1)) + stT55 64 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 63
    simpa using h
  have hprev := st55_p63
  have hstep := st55_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p65 : ((27528786532257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT55 (i+1))
      = (∑ i ∈ Finset.range 64, stT55 (i+1)) + stT55 65 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 64
    simpa using h
  have hprev := st55_p64
  have hstep := st55_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p66 : ((13311093430941/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT55 (i+1))
      = (∑ i ∈ Finset.range 65, stT55 (i+1)) + stT55 66 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 65
    simpa using h
  have hprev := st55_p65
  have hstep := st55_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p67 : ((13310597422771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT55 (i+1))
      = (∑ i ∈ Finset.range 66, stT55 (i+1)) + stT55 67 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 66
    simpa using h
  have hprev := st55_p66
  have hstep := st55_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p68 : ((550057108159/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT55 (i+1))
      = (∑ i ∈ Finset.range 67, stT55 (i+1)) + stT55 68 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 67
    simpa using h
  have hprev := st55_p67
  have hstep := st55_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p69 : ((7176342174641/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT55 (i+1))
      = (∑ i ∈ Finset.range 68, stT55 (i+1)) + stT55 69 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 68
    simpa using h
  have hprev := st55_p68
  have hstep := st55_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p70 : ((7376306209497/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT55 (i+1))
      = (∑ i ∈ Finset.range 69, stT55 (i+1)) + stT55 70 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 69
    simpa using h
  have hprev := st55_p69
  have hstep := st55_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p71 : ((14724736689987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT55 (i+1))
      = (∑ i ∈ Finset.range 70, stT55 (i+1)) + stT55 71 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 70
    simpa using h
  have hprev := st55_p70
  have hstep := st55_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p72 : ((14295410660947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT55 (i+1))
      = (∑ i ∈ Finset.range 71, stT55 (i+1)) + stT55 72 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 71
    simpa using h
  have hprev := st55_p71
  have hstep := st55_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p73 : ((2742036016459/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT55 (i+1))
      = (∑ i ∈ Finset.range 72, stT55 (i+1)) + stT55 73 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 72
    simpa using h
  have hprev := st55_p72
  have hstep := st55_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p74 : ((1062863335817/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT55 (i+1))
      = (∑ i ∈ Finset.range 73, stT55 (i+1)) + stT55 74 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 73
    simpa using h
  have hprev := st55_p73
  have hstep := st55_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p75 : ((13239511858983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT55 (i+1))
      = (∑ i ∈ Finset.range 74, stT55 (i+1)) + stT55 75 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 74
    simpa using h
  have hprev := st55_p74
  have hstep := st55_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p76 : ((13585800942247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT55 (i+1))
      = (∑ i ∈ Finset.range 75, stT55 (i+1)) + stT55 76 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 75
    simpa using h
  have hprev := st55_p75
  have hstep := st55_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p77 : ((28287625038229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT55 (i+1))
      = (∑ i ∈ Finset.range 76, stT55 (i+1)) + stT55 77 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 76
    simpa using h
  have hprev := st55_p76
  have hstep := st55_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p78 : ((14638939700921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT55 (i+1))
      = (∑ i ∈ Finset.range 77, stT55 (i+1)) + stT55 78 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 77
    simpa using h
  have hprev := st55_p77
  have hstep := st55_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p79 : ((29678373245971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT55 (i+1))
      = (∑ i ∈ Finset.range 78, stT55 (i+1)) + stT55 79 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 78
    simpa using h
  have hprev := st55_p78
  have hstep := st55_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p80 : ((29318321576611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT55 (i+1))
      = (∑ i ∈ Finset.range 79, stT55 (i+1)) + stT55 80 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 79
    simpa using h
  have hprev := st55_p79
  have hstep := st55_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p81 : ((28376709712211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT55 (i+1))
      = (∑ i ∈ Finset.range 80, stT55 (i+1)) + stT55 81 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 80
    simpa using h
  have hprev := st55_p80
  have hstep := st55_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p82 : ((27279649068331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT55 (i+1))
      = (∑ i ∈ Finset.range 81, stT55 (i+1)) + stT55 82 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 81
    simpa using h
  have hprev := st55_p81
  have hstep := st55_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p83 : ((26500658417089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT55 (i+1))
      = (∑ i ∈ Finset.range 82, stT55 (i+1)) + stT55 83 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 82
    simpa using h
  have hprev := st55_p82
  have hstep := st55_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p84 : ((26358834174529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT55 (i+1))
      = (∑ i ∈ Finset.range 83, stT55 (i+1)) + stT55 84 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 83
    simpa using h
  have hprev := st55_p83
  have hstep := st55_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p85 : ((26898279338817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT55 (i+1))
      = (∑ i ∈ Finset.range 84, stT55 (i+1)) + stT55 85 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 84
    simpa using h
  have hprev := st55_p84
  have hstep := st55_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p86 : ((5577700110591/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT55 (i+1))
      = (∑ i ∈ Finset.range 85, stT55 (i+1)) + stT55 86 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 85
    simpa using h
  have hprev := st55_p85
  have hstep := st55_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p87 : ((28932588617387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT55 (i+1))
      = (∑ i ∈ Finset.range 86, stT55 (i+1)) + stT55 87 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 86
    simpa using h
  have hprev := st55_p86
  have hstep := st55_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p88 : ((1851878249639/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT55 (i+1))
      = (∑ i ∈ Finset.range 87, stT55 (i+1)) + stT55 88 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 87
    simpa using h
  have hprev := st55_p87
  have hstep := st55_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p89 : ((3715898764913/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT55 (i+1))
      = (∑ i ∈ Finset.range 88, stT55 (i+1)) + stT55 89 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 88
    simpa using h
  have hprev := st55_p88
  have hstep := st55_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p90 : ((14600450229039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT55 (i+1))
      = (∑ i ∈ Finset.range 89, stT55 (i+1)) + stT55 90 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 89
    simpa using h
  have hprev := st55_p89
  have hstep := st55_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p91 : ((14126281571559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT55 (i+1))
      = (∑ i ∈ Finset.range 90, stT55 (i+1)) + stT55 91 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 90
    simpa using h
  have hprev := st55_p90
  have hstep := st55_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p92 : ((27223379908157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT55 (i+1))
      = (∑ i ∈ Finset.range 91, stT55 (i+1)) + stT55 92 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 91
    simpa using h
  have hprev := st55_p91
  have hstep := st55_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p93 : ((26468399006853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT55 (i+1))
      = (∑ i ∈ Finset.range 92, stT55 (i+1)) + stT55 93 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 92
    simpa using h
  have hprev := st55_p92
  have hstep := st55_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p94 : ((1049440826467/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT55 (i+1))
      = (∑ i ∈ Finset.range 93, stT55 (i+1)) + stT55 94 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 93
    simpa using h
  have hprev := st55_p93
  have hstep := st55_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p95 : ((26592413613557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT55 (i+1))
      = (∑ i ∈ Finset.range 94, stT55 (i+1)) + stT55 95 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 94
    simpa using h
  have hprev := st55_p94
  have hstep := st55_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p96 : ((27410962080377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT55 (i+1))
      = (∑ i ∈ Finset.range 95, stT55 (i+1)) + stT55 96 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 95
    simpa using h
  have hprev := st55_p95
  have hstep := st55_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p97 : ((28423763623301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT55 (i+1))
      = (∑ i ∈ Finset.range 96, stT55 (i+1)) + stT55 97 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 96
    simpa using h
  have hprev := st55_p96
  have hstep := st55_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p98 : ((5862618672577/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT55 (i+1))
      = (∑ i ∈ Finset.range 97, stT55 (i+1)) + stT55 98 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 97
    simpa using h
  have hprev := st55_p97
  have hstep := st55_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p99 : ((29811040954609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT55 (i+1))
      = (∑ i ∈ Finset.range 98, stT55 (i+1)) + stT55 99 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 98
    simpa using h
  have hprev := st55_p98
  have hstep := st55_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st55_p100 : ((29776641954609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT55 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT55 (i+1))
      = (∑ i ∈ Finset.range 99, stT55 (i+1)) + stT55 100 := by
    have h := Finset.sum_range_succ (fun i => stT55 (i+1)) 99
    simpa using h
  have hprev := st55_p99
  have hstep := st55_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 55`.** -/
theorem station_55_sign : 0 < hardyG (((55:ℕ)):ℝ) := by
  have hcore := phase_station_lower 55 100 (by norm_num) (by norm_num)
    ((87949/250000 : ℚ) : ℝ)
  have hchain := st55_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT55 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((55:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((87949/250000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((55:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((55:ℕ)):ℝ)+1) * ((((55:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((551989/1100000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((29776641954609/10000000000000 : ℚ) : ℝ) - ((551989/1100000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((87949/250000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((55:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((87949/250000 : ℚ) : ℝ)
        * (riemannZeta (line (((55:ℕ)):ℝ))).re
      - Real.sin ((87949/250000 : ℚ) : ℝ)
        * (riemannZeta (line (((55:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((55:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((55:ℕ)):ℝ)
      = ((((55:ℕ)):ℝ) * (Real.log (((55:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((55:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_55
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
  have hθwin : |(((87949/250000 : ℚ) : ℝ) + ((5:ℤ)) * (2*Real.pi)) - theta (((55:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((55:ℕ)):ℝ))
    (φ := ((87949/250000 : ℚ) : ℝ) + ((5:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((87949/250000 : ℚ)) : ℝ) 5).1,
    (cos_sin_shift (((87949/250000 : ℚ)) : ℝ) 5).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_55_sign
end AxiomAudit
