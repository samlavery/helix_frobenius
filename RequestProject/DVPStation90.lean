import RequestProject.DVPSqrtTable

/-!
# Station `t = 90` of the extended Hardy ladder (rung-91)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT90 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((90 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-250931/250000 : ℚ) : ℝ))

theorem st90_c1 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((107433/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 250931/1000000) (δ := 1/100000000) (ψ := -250931/250000) 90 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t1 : ((107423/200000 : ℚ) : ℝ) ≤ stT90 1 := by
  have hc : ((107423/200000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107423/200000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((107423/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c2 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((849839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 86737/625000) (δ := 689/100000000) (ψ := -250931/250000) 90 10
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t2 : ((6008914954863/10000000000000 : ℚ) : ℝ) ≤ stT90 2 := by
  have hc : ((849789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6008914954863/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((849789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c3 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((79479/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -815169/5000000) (δ := 773/100000000) (ψ := -250931/250000) 90 16
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t3 : ((114710824487/250000000000 : ℚ) : ℝ) ≤ stT90 3 := by
  have hc : ((39737/50000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114710824487/250000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((39737/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c4 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((994333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10651/400000) (δ := 129/25000000) (ψ := -250931/250000) 90 20
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t4 : ((994283/2000000 : ℚ) : ℝ) ≤ stT90 4 := by
  have hc : ((994283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((994283/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((994283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c5 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((1831/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 669937/2000000) (δ := 159/20000000) (ψ := -250931/250000) 90 23
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t5 : ((8186690331/80000000000 : ℚ) : ℝ) ≤ stT90 5 := by
  have hc : ((9153/40000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8186690331/80000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((9153/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c6 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((90587/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -550371/2000000) (δ := 3/500000) (ψ := -250931/250000) 90 26
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t6 : ((184889486057/1000000000000 : ℚ) : ℝ) ≤ stT90 6 := by
  have hc : ((90577/200000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184889486057/1000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((90577/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c7 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((195753/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 258061/5000000) (δ := 461/100000000) (ψ := -250931/250000) 90 28
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t7 : ((184959713873/500000000000 : ℚ) : ℝ) ≤ stT90 7 := by
  have hc : ((195743/200000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184959713873/500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((195743/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c8 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((942053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -427621/5000000) (δ := 7/1250000) (ψ := -250931/250000) 90 30
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t8 : ((3330482692599/10000000000000 : ℚ) : ℝ) ≤ stT90 8 := by
  have hc : ((942003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3330482692599/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((942003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c9 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-84027/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1153997/2000000) (δ := 171/25000000) (ψ := -250931/250000) 90 32
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t9 : ((-560221778711/2500000000000 : ℚ) : ℝ) ≤ stT90 9 := by
  have hc : ((-336133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-560221778711/2500000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-336133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c10 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((628427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 278521/1250000) (δ := 167/20000000) (ψ := -250931/250000) 90 33
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t10 : ((1987102134429/10000000000000 : ℚ) : ℝ) ≤ stT90 10 := by
  have hc : ((628377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1987102134429/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((628377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c11 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-499507/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -967871/1250000) (δ := 657/100000000) (ψ := -250931/250000) 90 35
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t11 : ((-188268240831/625000000000 : ℚ) : ℝ) ≤ stT90 11 := by
  have hc : ((-124883/125000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188268240831/625000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-124883/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c12 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((10723/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -968343/2500000) (δ := 119/25000000) (ψ := -250931/250000) 90 36
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t12 : ((15441231099/2500000000000 : ℚ) : ℝ) ≤ stT90 12 := by
  have hc : ((5349/250000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15441231099/2500000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((5349/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c13 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((404399/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -785863/5000000) (δ := 249/50000000) (ψ := -250931/250000) 90 37
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t13 : ((1121531289/5000000000 : ℚ) : ℝ) ≤ stT90 13 := by
  have hc : ((202187/250000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1121531289/5000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((202187/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c14 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((970823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -151349/2500000) (δ := 337/50000000) (ψ := -250931/250000) 90 38
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t14 : ((648624892269/2500000000000 : ℚ) : ℝ) ≤ stT90 14 := by
  have hc : ((970773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((648624892269/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((970773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c15 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((950491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -789963/10000000) (δ := 923/100000000) (ψ := -250931/250000) 90 39
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t15 : ((613506814177/2500000000000 : ℚ) : ℝ) ≤ stT90 15 := by
  have hc : ((950441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((613506814177/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((950441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c16 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((140669/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1976759/10000000) (δ := 733/100000000) (ψ := -250931/250000) 90 40
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t16 : ((140659/800000 : ℚ) : ℝ) ≤ stT90 16 := by
  have hc : ((140659/200000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140659/800000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((140659/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c17 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-46859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2022091/5000000) (δ := 261/50000000) (ψ := -250931/250000) 90 41
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t17 : ((-113771071513/10000000000000 : ℚ) : ℝ) ≤ stT90 17 := by
  have hc : ((-46909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113771071513/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-46909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c18 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-926801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3445751/5000000) (δ := 2/390625) (ψ := -250931/250000) 90 42
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t18 : ((-2184609124573/10000000000000 : ℚ) : ℝ) ≤ stT90 18 := by
  have hc : ((-926851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2184609124573/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-926851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c19 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-25649/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5273623/10000000) (δ := 89/12500000) (ψ := -250931/250000) 90 42
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t19 : ((-58848593937/500000000000 : ℚ) : ℝ) ≤ stT90 19 := by
  have hc : ((-51303/100000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58848593937/500000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-51303/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c20 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((180723/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1106651/10000000) (δ := 331/50000000) (ψ := -250931/250000) 90 43
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t20 : ((404086375771/2000000000000 : ℚ) : ℝ) ≤ stT90 20 := by
  have hc : ((180713/200000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((404086375771/2000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((180713/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c21 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((1892/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1811763/5000000) (δ := 59/10000000) (ψ := -250931/250000) 90 44
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t21 : ((66031615191/2500000000000 : ℚ) : ℝ) ≤ stT90 21 := by
  have hc : ((60519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66031615191/2500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((60519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c22 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-919417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3421739/5000000) (δ := 473/100000000) (ψ := -250931/250000) 90 44
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t22 : ((-245038874967/1250000000000 : ℚ) : ℝ) ≤ stT90 22 := by
  have hc : ((-919467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245038874967/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-919467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c23 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((898321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1137161/10000000) (δ := 779/100000000) (ψ := -250931/250000) 90 45
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t23 : ((234128048253/1250000000000 : ℚ) : ℝ) ≤ stT90 23 := by
  have hc : ((898271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234128048253/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((898271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c24 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-414287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4994889/10000000) (δ := 81/12500000) (ψ := -250931/250000) 90 46
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t24 : ((-422881043277/5000000000000 : ℚ) : ℝ) ≤ stT90 24 := by
  have hc : ((-414337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-422881043277/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-414337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c25 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-52517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 209503/500000) (δ := 43/6250000) (ψ := -250931/250000) 90 46
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t25 : ((-52542026271/2500000000000 : ℚ) : ℝ) ≤ stT90 25 := by
  have hc : ((-26271/250000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52542026271/2500000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-26271/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c26 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((47371/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2693243/10000000) (δ := 289/50000000) (ψ := -250931/250000) 90 47
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t26 : ((46446175963/500000000000 : ℚ) : ℝ) ≤ stT90 26 := by
  have hc : ((23683/50000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46446175963/500000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((23683/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c27 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-680567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5798331/10000000) (δ := 117/20000000) (ψ := -250931/250000) 90 47
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t27 : ((-1309848097117/10000000000000 : ℚ) : ℝ) ≤ stT90 27 := by
  have hc : ((-680617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1309848097117/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-680617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c28 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((770759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1726913/10000000) (δ := 847/100000000) (ψ := -250931/250000) 90 48
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t28 : ((728251411899/5000000000000 : ℚ) : ℝ) ≤ stT90 28 := by
  have hc : ((770709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((728251411899/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((770709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c29 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-156249/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3084317/5000000) (δ := 667/100000000) (ψ := -250931/250000) 90 48
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t29 : ((-145082887543/1000000000000 : ℚ) : ℝ) ≤ stT90 29 := by
  have hc : ((-156259/200000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145082887543/1000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-156259/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c30 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((144333/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47787/250000) (δ := 707/100000000) (ψ := -250931/250000) 90 49
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t30 : ((263496418343/2000000000000 : ℚ) : ℝ) ≤ stT90 30 := by
  have hc : ((144323/200000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((263496418343/2000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((144323/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c31 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-577527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 546623/1000000) (δ := 7/781250) (ψ := -250931/250000) 90 49
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t31 : ((-518679740579/5000000000000 : ℚ) : ℝ) ≤ stT90 31 := by
  have hc : ((-577577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-518679740579/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-577577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c32 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((40681/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -774569/2500000) (δ := 453/50000000) (ψ := -250931/250000) 90 50
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t32 : ((143806880217/2500000000000 : ℚ) : ℝ) ≤ stT90 32 := by
  have hc : ((162699/500000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143806880217/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((162699/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c33 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((20323/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3825347/10000000) (δ := 517/100000000) (ψ := -250931/250000) 90 50
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t33 : ((2208391953/312500000000 : ℚ) : ℝ) ≤ stT90 33 := by
  have hc : ((10149/250000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2208391953/312500000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((10149/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c34 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-475457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5165699/10000000) (δ := 139/20000000) (ψ := -250931/250000) 90 51
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t34 : ((-407743923951/5000000000000 : ℚ) : ℝ) ≤ stT90 34 := by
  have hc : ((-475507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-407743923951/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-475507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c35 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((85637/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1356497/10000000) (δ := 137/25000000) (ψ := -250931/250000) 90 51
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t35 : ((282704013/1953125000 : ℚ) : ℝ) ≤ stT90 35 := by
  have hc : ((2676/3125 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((282704013/1953125000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((2676/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c36 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-997977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 240467/312500) (δ := 23/4000000) (ψ := -250931/250000) 90 51
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t36 : ((-1663378666009/10000000000000 : ℚ) : ℝ) ≤ stT90 36 := by
  have hc : ((-998027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1663378666009/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-998027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c37 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((36947/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7393/40000) (δ := 201/25000000) (ψ := -250931/250000) 90 52
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t37 : ((121472703221/1000000000000 : ℚ) : ℝ) ≤ stT90 37 := by
  have hc : ((73889/100000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121472703221/1000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((73889/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c38 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-22481/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2076053/5000000) (δ := 539/100000000) (ψ := -250931/250000) 90 52
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t38 : ((-14595717241/1000000000000 : ℚ) : ℝ) ≤ stT90 38 := by
  have hc : ((-44987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14595717241/1000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-44987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c39 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-26187/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5711373/10000000) (δ := 493/100000000) (ψ := -250931/250000) 90 53
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t39 : ((-20967987149/200000000000 : ℚ) : ℝ) ≤ stT90 39 := by
  have hc : ((-26189/40000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20967987149/200000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-26189/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c40 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((499991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14867/10000000) (δ := 453/100000000) (ψ := -250931/250000) 90 53
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t40 : ((197628810327/1250000000000 : ℚ) : ℝ) ≤ stT90 40 := by
  have hc : ((249983/250000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197628810327/1250000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((249983/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c41 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-601671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5540971/10000000) (δ := 57/10000000) (ψ := -250931/250000) 90 53
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t41 : ((-469865275549/5000000000000 : ℚ) : ℝ) ≤ stT90 41 := by
  have hc : ((-601721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-469865275549/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-601721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c42 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-321413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4745043/10000000) (δ := 763/100000000) (ψ := -250931/250000) 90 54
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t42 : ((-248014169371/5000000000000 : ℚ) : ℝ) ≤ stT90 42 := by
  have hc : ((-321463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-248014169371/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-321463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c43 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((975957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 549319/10000000) (δ := 783/100000000) (ψ := -250931/250000) 90 54
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t43 : ((297648707279/2000000000000 : ℚ) : ℝ) ≤ stT90 43 := by
  have hc : ((975907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((297648707279/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((975907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c44 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-657871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5721961/10000000) (δ := 603/100000000) (ψ := -250931/250000) 90 54
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t44 : ((-991853408997/10000000000000 : ℚ) : ℝ) ≤ stT90 44 := by
  have hc : ((-657921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-991853408997/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-657921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c45 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-390383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -492961/1000000) (δ := 791/100000000) (ψ := -250931/250000) 90 55
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t45 : ((-72752894787/1250000000000 : ℚ) : ℝ) ≤ stT90 45 := by
  have hc : ((-390433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72752894787/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-390433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c46 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((49999/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3911/2500000) (δ := 851/100000000) (ψ := -250931/250000) 90 55
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t46 : ((147431579067/1000000000000 : ℚ) : ℝ) ≤ stT90 46 := by
  have hc : ((99993/100000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147431579067/1000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((99993/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c47 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-181283/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 242727/500000) (δ := 57/6250000) (ψ := -250931/250000) 90 55
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t47 : ((-1322324571/25000000000 : ℚ) : ℝ) ≤ stT90 47 := by
  have hc : ((-45327/125000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1322324571/25000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-45327/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c48 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-384017/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3058203/5000000) (δ := 821/100000000) (ψ := -250931/250000) 90 56
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t48 : ((-17322406431/156250000000 : ℚ) : ℝ) ≤ stT90 48 := by
  have hc : ((-192021/250000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17322406431/156250000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-192021/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c49 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((830481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -738533/5000000) (δ := 441/50000000) (ψ := -250931/250000) 90 56
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t49 : ((1186329644101/10000000000000 : ℚ) : ℝ) ≤ stT90 49 := by
  have hc : ((830431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1186329644101/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((830431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c50 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((336671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3068543/10000000) (δ := 861/100000000) (ψ := -250931/250000) 90 56
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t50 : ((476053794273/10000000000000 : ℚ) : ℝ) ≤ stT90 50 := by
  have hc : ((336621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((476053794273/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((336621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c51 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-991309/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3762067/5000000) (δ := 621/100000000) (ψ := -250931/250000) 90 56
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t51 : ((-1388181171879/10000000000000 : ℚ) : ℝ) ≤ stT90 51 := by
  have hc : ((-991359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1388181171879/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-991359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c52 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((44877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -95369/250000) (δ := 751/100000000) (ψ := -250931/250000) 90 57
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t52 : ((248655369/40000000000 : ℚ) : ℝ) ≤ stT90 52 := by
  have hc : ((44827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((248655369/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((44827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c53 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((982299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 117771/2500000) (δ := 791/100000000) (ψ := -250931/250000) 90 57
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t53 : ((269844427529/2000000000000 : ℚ) : ℝ) ≤ stT90 53 := by
  have hc : ((982249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((269844427529/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((982249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c54 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-295453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2338407/5000000) (δ := 491/100000000) (ψ := -250931/250000) 90 57
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t54 : ((-100532189121/2500000000000 : ℚ) : ℝ) ≤ stT90 54 := by
  have hc : ((-295503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100532189121/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-295503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c55 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-464229/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6902593/10000000) (δ := 763/100000000) (ψ := -250931/250000) 90 58
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t55 : ((-782500117/6250000000 : ℚ) : ℝ) ≤ stT90 55 := by
  have hc : ((-232127/250000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-782500117/6250000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-232127/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c56 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((83633/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -284843/1000000) (δ := 783/100000000) (ψ := -250931/250000) 90 58
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t56 : ((55872958319/1000000000000 : ℚ) : ℝ) ≤ stT90 56 := by
  have hc : ((83623/200000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55872958319/1000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((83623/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c57 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((2809/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45359/400000) (δ := 583/100000000) (ψ := -250931/250000) 90 58
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t57 : ((29763227439/250000000000 : ℚ) : ℝ) ≤ stT90 57 := by
  have hc : ((89883/100000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29763227439/250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((89883/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c58 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-433209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5047117/10000000) (δ := 21/2500000) (ψ := -250931/250000) 90 58
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t58 : ((-113779445767/2000000000000 : ℚ) : ℝ) ≤ stT90 58 := by
  have hc : ((-433259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113779445767/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-433259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c59 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-228703/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3407299/5000000) (δ := 509/100000000) (ψ := -250931/250000) 90 59
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t59 : ((-59552484459/500000000000 : ℚ) : ℝ) ≤ stT90 59 := by
  have hc : ((-457431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59552484459/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-457431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c60 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((14001/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3032997/10000000) (δ := 267/50000000) (ψ := -250931/250000) 90 59
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t60 : ((9036312503/200000000000 : ℚ) : ℝ) ≤ stT90 60 := by
  have hc : ((13999/40000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9036312503/200000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((13999/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c61 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((481289/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42881/625000) (δ := 277/50000000) (ψ := -250931/250000) 90 59
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t61 : ((2407011817/19531250000 : ℚ) : ℝ) ≤ stT90 61 := by
  have hc : ((30079/31250 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2407011817/19531250000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((30079/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c62 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-20789/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4344713/10000000) (δ := 367/50000000) (ψ := -250931/250000) 90 59
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t62 : ((-52820018181/2500000000000 : ℚ) : ℝ) ≤ stT90 62 := by
  have hc : ((-83181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52820018181/2500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-83181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c63 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-49967/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7763173/10000000) (δ := 339/50000000) (ψ := -250931/250000) 90 60
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t63 : ((-62955673599/500000000000 : ℚ) : ℝ) ≤ stT90 63 := by
  have hc : ((-99939/100000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62955673599/500000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-99939/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c64 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-116853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4219793/10000000) (δ := 29/4000000) (ψ := -250931/250000) 90 60
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t64 : ((-146128866903/10000000000000 : ℚ) : ℝ) ≤ stT90 64 := by
  have hc : ((-116903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146128866903/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-116903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c65 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((478757/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -731351/10000000) (δ := 121/20000000) (ψ := -250931/250000) 90 60
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t65 : ((148448450001/1250000000000 : ℚ) : ℝ) ≤ stT90 65 := by
  have hc : ((119683/125000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148448450001/1250000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((119683/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c66 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((469977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 270383/1000000) (δ := 279/50000000) (ψ := -250931/250000) 90 60
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t66 : ((289219861639/5000000000000 : ℚ) : ℝ) ≤ stT90 66 := by
  have hc : ((469927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((289219861639/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((469927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c67 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-38027/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6087353/10000000) (δ := 369/50000000) (ψ := -250931/250000) 90 60
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t67 : ((-18584180001/200000000000 : ℚ) : ℝ) ≤ stT90 67 := by
  have hc : ((-76059/100000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18584180001/200000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-76059/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c68 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-202491/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -392951/625000) (δ := 217/25000000) (ψ := -250931/250000) 90 61
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t68 : ((-491143483753/5000000000000 : ℚ) : ℝ) ≤ stT90 68 := by
  have hc : ((-405007/500000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-491143483753/5000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-405007/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c69 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((361431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1501243/5000000) (δ := 217/25000000) (ψ := -250931/250000) 90 61
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t69 : ((217525703949/5000000000000 : ℚ) : ℝ) ≤ stT90 69 := by
  have hc : ((361381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217525703949/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((361381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c70 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((497793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11749/500000) (δ := 33/6250000) (ψ := -250931/250000) 90 61
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t70 : ((18592070347/156250000000 : ℚ) : ℝ) ≤ stT90 70 := by
  have hc : ((62221/62500 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18592070347/156250000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((62221/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c71 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((198853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1713261/5000000) (δ := 131/20000000) (ψ := -250931/250000) 90 61
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t71 : ((235935623143/10000000000000 : ℚ) : ℝ) ≤ stT90 71 := by
  have hc : ((198803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235935623143/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((198803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c72 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-435829/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6573427/10000000) (δ := 187/25000000) (ψ := -250931/250000) 90 61
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t72 : ((-16051849039/156250000000 : ℚ) : ℝ) ≤ stT90 72 := by
  have hc : ((-217927/250000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16051849039/156250000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-217927/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c73 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-745723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6031039/10000000) (δ := 557/100000000) (ψ := -250931/250000) 90 62
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t73 : ((-218215417119/2500000000000 : ℚ) : ℝ) ≤ stT90 73 := by
  have hc : ((-745773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218215417119/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-745773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c74 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((186801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2969767/10000000) (δ := 413/50000000) (ψ := -250931/250000) 90 62
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t74 : ((6785081793/156250000000 : ℚ) : ℝ) ≤ stT90 74 := by
  have hc : ((23347/62500 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6785081793/156250000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((23347/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c75 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((999797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12603/2500000) (δ := 817/100000000) (ψ := -250931/250000) 90 62
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t75 : ((11544078609/100000000000 : ℚ) : ℝ) ≤ stT90 75 := by
  have hc : ((999747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11544078609/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((999747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c76 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((350927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 757647/2500000) (δ := 577/100000000) (ψ := -250931/250000) 90 62
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t76 : ((201241643703/5000000000000 : ℚ) : ℝ) ≤ stT90 76 := by
  have hc : ((350877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201241643703/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((350877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c77 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-72973/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5971807/10000000) (δ := 717/100000000) (ψ := -250931/250000) 90 62
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t77 : ((-20791541667/250000000000 : ℚ) : ℝ) ≤ stT90 77 := by
  have hc : ((-36489/50000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20791541667/250000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-36489/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c78 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-917743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -683289/1000000) (δ := 333/50000000) (ψ := -250931/250000) 90 63
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t78 : ((-519598411227/5000000000000 : ℚ) : ℝ) ≤ stT90 78 := by
  have hc : ((-917793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-519598411227/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-917793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c79 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-15847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -396661/1000000) (δ := 233/50000000) (ψ := -250931/250000) 90 63
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t79 : ((-558922623/312500000000 : ℚ) : ℝ) ≤ stT90 79 := by
  have hc : ((-15897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-558922623/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-15897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c80 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((898457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8878/78125) (δ := 313/50000000) (ψ := -250931/250000) 90 63
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t80 : ((1004448673431/10000000000000 : ℚ) : ℝ) ≤ stT90 80 := by
  have hc : ((898407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1004448673431/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((898407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c81 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((393929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1658683/10000000) (δ := 457/100000000) (ψ := -250931/250000) 90 63
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t81 : ((27354441709/312500000000 : ℚ) : ℝ) ≤ stT90 81 := by
  have hc : ((24619/31250 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27354441709/312500000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((24619/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c82 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-97857/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2209727/5000000) (δ := 253/50000000) (ψ := -250931/250000) 90 63
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t82 : ((-13511582339/625000000000 : ℚ) : ℝ) ≤ stT90 82 := by
  have hc : ((-48941/250000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13511582339/625000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-48941/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c83 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-960253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 178669/250000) (δ := 433/50000000) (ψ := -250931/250000) 90 63
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t83 : ((-1054069865829/10000000000000 : ℚ) : ℝ) ≤ stT90 83 := by
  have hc : ((-960303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1054069865829/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-960303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c84 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-700307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18333/31250) (δ := 117/12500000) (ψ := -250931/250000) 90 64
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t84 : ((-76415251913/1000000000000 : ℚ) : ℝ) ≤ stT90 84 := by
  have hc : ((-700357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76415251913/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-700357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c85 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((35657/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3203807/10000000) (δ := 487/100000000) (ψ := -250931/250000) 90 64
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t85 : ((38668657289/1250000000000 : ℚ) : ℝ) ≤ stT90 85 := by
  have hc : ((142603/500000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38668657289/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((142603/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c86 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((973921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -286099/5000000) (δ := 847/100000000) (ψ := -250931/250000) 90 64
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t86 : ((1050151393817/10000000000000 : ℚ) : ℝ) ≤ stT90 86 := by
  have hc : ((973871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1050151393817/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((973871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c87 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((344171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2028987/10000000) (δ := 189/25000000) (ψ := -250931/250000) 90 64
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t87 : ((11530095511/156250000000 : ℚ) : ℝ) ≤ stT90 87 := by
  have hc : ((172073/250000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11530095511/156250000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((172073/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c88 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-53227/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1150111/2500000) (δ := 97/12500000) (ψ := -250931/250000) 90 64
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t88 : ((-14187713737/500000000000 : ℚ) : ℝ) ≤ stT90 88 := by
  have hc : ((-53237/200000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14187713737/500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-53237/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c89 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-191963/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1785711/2500000) (δ := 627/100000000) (ψ := -250931/250000) 90 64
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t89 : ((-101745498027/1000000000000 : ℚ) : ℝ) ≤ stT90 89 := by
  have hc : ((-191973/200000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101745498027/1000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-191973/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c90 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-187763/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6051127/10000000) (δ := 309/50000000) (ψ := -250931/250000) 90 65
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t90 : ((-395865680243/5000000000000 : ℚ) : ℝ) ≤ stT90 90 := by
  have hc : ((-375551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-395865680243/5000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-375551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c91 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((5773/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1782457/5000000) (δ := 469/50000000) (ψ := -250931/250000) 90 65
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t91 : ((1512411741/100000000000 : ℚ) : ℝ) ≤ stT90 91 := by
  have hc : ((5771/40000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1512411741/100000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((5771/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c92 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((903749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1105873/10000000) (δ := 339/50000000) (ψ := -250931/250000) 90 65
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t92 : ((235542818457/2500000000000 : ℚ) : ℝ) ≤ stT90 92 := by
  have hc : ((903699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235542818457/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((903699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c93 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((862487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1326583/10000000) (δ := 409/50000000) (ψ := -250931/250000) 90 65
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t93 : ((894304909587/10000000000000 : ℚ) : ℝ) ≤ stT90 93 := by
  have hc : ((862437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((894304909587/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((862437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c94 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((77509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3733023/10000000) (δ := 359/50000000) (ψ := -250931/250000) 90 65
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t94 : ((79892839239/10000000000000 : ℚ) : ℝ) ≤ stT90 94 := by
  have hc : ((77459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79892839239/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((77459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c95 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-767417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3056999/5000000) (δ := 409/50000000) (ψ := -250931/250000) 90 65
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t95 : ((-787405025193/10000000000000 : ℚ) : ℝ) ≤ stT90 95 := by
  have hc : ((-767467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-787405025193/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-767467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c96 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-969791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7237923/10000000) (δ := 809/100000000) (ψ := -250931/250000) 90 66
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t96 : ((-989840091261/10000000000000 : ℚ) : ℝ) ≤ stT90 96 := by
  have hc : ((-969841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-989840091261/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-969841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c97 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((-381781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -613287/1250000) (δ := 689/100000000) (ψ := -250931/250000) 90 66
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t97 : ((-387690960357/10000000000000 : ℚ) : ℝ) ≤ stT90 97 := by
  have hc : ((-381831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-387690960357/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-381831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c98 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((506709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2598583/10000000) (δ := 709/100000000) (ψ := -250931/250000) 90 66
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t98 : ((63975325271/1250000000000 : ℚ) : ℝ) ≤ stT90 98 := by
  have hc : ((506659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63975325271/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((506659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c99 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((248027/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3143/100000) (δ := 237/50000000) (ψ := -250931/250000) 90 66
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t99 : ((498527498073/5000000000000 : ℚ) : ℝ) ≤ stT90 99 := by
  have hc : ((496029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((498527498073/5000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((496029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_c100 :
    |Real.cos (((90 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-250931/250000 : ℚ) : ℝ))
      - ((2847/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 973513/5000000) (δ := 769/100000000) (ψ := -250931/250000) 90 66
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st90_t100 : ((7116992883/100000000000 : ℚ) : ℝ) ≤ stT90 100 := by
  have hc : ((7117/10000 : ℚ) : ℝ)
      ≤ Real.cos (((90 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-250931/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st90_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7116992883/100000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((7117/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st90_p1 : ((107423/200000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT90 (i+1) := by
  rw [Finset.sum_range_one]
  exact st90_t1

theorem st90_p2 : ((11380064954863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT90 (i+1))
      = (∑ i ∈ Finset.range 1, stT90 (i+1)) + stT90 2 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 1
    simpa using h
  have hprev := st90_p1
  have hstep := st90_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p3 : ((15968497934343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT90 (i+1))
      = (∑ i ∈ Finset.range 2, stT90 (i+1)) + stT90 3 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 2
    simpa using h
  have hprev := st90_p2
  have hstep := st90_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p4 : ((20939912934343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT90 (i+1))
      = (∑ i ∈ Finset.range 3, stT90 (i+1)) + stT90 4 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 3
    simpa using h
  have hprev := st90_p3
  have hstep := st90_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p5 : ((10981624612859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT90 (i+1))
      = (∑ i ∈ Finset.range 4, stT90 (i+1)) + stT90 5 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 4
    simpa using h
  have hprev := st90_p4
  have hstep := st90_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p6 : ((1488259005393/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT90 (i+1))
      = (∑ i ∈ Finset.range 5, stT90 (i+1)) + stT90 6 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 5
    simpa using h
  have hprev := st90_p5
  have hstep := st90_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p7 : ((6877834590937/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT90 (i+1))
      = (∑ i ∈ Finset.range 6, stT90 (i+1)) + stT90 7 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 6
    simpa using h
  have hprev := st90_p6
  have hstep := st90_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p8 : ((30841821056347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT90 (i+1))
      = (∑ i ∈ Finset.range 7, stT90 (i+1)) + stT90 8 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 7
    simpa using h
  have hprev := st90_p7
  have hstep := st90_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p9 : ((28600933941503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT90 (i+1))
      = (∑ i ∈ Finset.range 8, stT90 (i+1)) + stT90 9 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 8
    simpa using h
  have hprev := st90_p8
  have hstep := st90_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p10 : ((7647009018983/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT90 (i+1))
      = (∑ i ∈ Finset.range 9, stT90 (i+1)) + stT90 10 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 9
    simpa using h
  have hprev := st90_p9
  have hstep := st90_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p11 : ((6893936055659/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT90 (i+1))
      = (∑ i ∈ Finset.range 10, stT90 (i+1)) + stT90 11 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 10
    simpa using h
  have hprev := st90_p10
  have hstep := st90_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p12 : ((3454688643379/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT90 (i+1))
      = (∑ i ∈ Finset.range 11, stT90 (i+1)) + stT90 12 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 11
    simpa using h
  have hprev := st90_p11
  have hstep := st90_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p13 : ((3735071465629/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT90 (i+1))
      = (∑ i ∈ Finset.range 12, stT90 (i+1)) + stT90 13 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 12
    simpa using h
  have hprev := st90_p12
  have hstep := st90_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p14 : ((8118767823527/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT90 (i+1))
      = (∑ i ∈ Finset.range 13, stT90 (i+1)) + stT90 14 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 13
    simpa using h
  have hprev := st90_p13
  have hstep := st90_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p15 : ((1091534329713/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT90 (i+1))
      = (∑ i ∈ Finset.range 14, stT90 (i+1)) + stT90 15 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 14
    simpa using h
  have hprev := st90_p14
  have hstep := st90_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p16 : ((286619812897/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT90 (i+1))
      = (∑ i ∈ Finset.range 15, stT90 (i+1)) + stT90 16 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 15
    simpa using h
  have hprev := st90_p15
  have hstep := st90_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p17 : ((36573564979303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT90 (i+1))
      = (∑ i ∈ Finset.range 16, stT90 (i+1)) + stT90 17 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 16
    simpa using h
  have hprev := st90_p16
  have hstep := st90_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p18 : ((3438895585473/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT90 (i+1))
      = (∑ i ∈ Finset.range 17, stT90 (i+1)) + stT90 18 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 17
    simpa using h
  have hprev := st90_p17
  have hstep := st90_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p19 : ((3321198397599/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT90 (i+1))
      = (∑ i ∈ Finset.range 18, stT90 (i+1)) + stT90 19 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 18
    simpa using h
  have hprev := st90_p18
  have hstep := st90_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p20 : ((7046483170969/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT90 (i+1))
      = (∑ i ∈ Finset.range 19, stT90 (i+1)) + stT90 20 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 19
    simpa using h
  have hprev := st90_p19
  have hstep := st90_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p21 : ((35496542315609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT90 (i+1))
      = (∑ i ∈ Finset.range 20, stT90 (i+1)) + stT90 21 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 20
    simpa using h
  have hprev := st90_p20
  have hstep := st90_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p22 : ((33536231315873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT90 (i+1))
      = (∑ i ∈ Finset.range 21, stT90 (i+1)) + stT90 22 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 21
    simpa using h
  have hprev := st90_p21
  have hstep := st90_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p23 : ((35409255701897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT90 (i+1))
      = (∑ i ∈ Finset.range 22, stT90 (i+1)) + stT90 23 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 22
    simpa using h
  have hprev := st90_p22
  have hstep := st90_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p24 : ((34563493615343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT90 (i+1))
      = (∑ i ∈ Finset.range 23, stT90 (i+1)) + stT90 24 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 23
    simpa using h
  have hprev := st90_p23
  have hstep := st90_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p25 : ((34353325510259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT90 (i+1))
      = (∑ i ∈ Finset.range 24, stT90 (i+1)) + stT90 25 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 24
    simpa using h
  have hprev := st90_p24
  have hstep := st90_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p26 : ((35282249029519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT90 (i+1))
      = (∑ i ∈ Finset.range 25, stT90 (i+1)) + stT90 26 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 25
    simpa using h
  have hprev := st90_p25
  have hstep := st90_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p27 : ((16986200466201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT90 (i+1))
      = (∑ i ∈ Finset.range 26, stT90 (i+1)) + stT90 27 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 26
    simpa using h
  have hprev := st90_p26
  have hstep := st90_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p28 : ((177144518781/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT90 (i+1))
      = (∑ i ∈ Finset.range 27, stT90 (i+1)) + stT90 28 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 27
    simpa using h
  have hprev := st90_p27
  have hstep := st90_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p29 : ((3397807488077/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT90 (i+1))
      = (∑ i ∈ Finset.range 28, stT90 (i+1)) + stT90 29 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 28
    simpa using h
  have hprev := st90_p28
  have hstep := st90_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p30 : ((7059111394497/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT90 (i+1))
      = (∑ i ∈ Finset.range 29, stT90 (i+1)) + stT90 30 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 29
    simpa using h
  have hprev := st90_p29
  have hstep := st90_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p31 : ((34258197491327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT90 (i+1))
      = (∑ i ∈ Finset.range 30, stT90 (i+1)) + stT90 31 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 30
    simpa using h
  have hprev := st90_p30
  have hstep := st90_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p32 : ((6966685002439/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT90 (i+1))
      = (∑ i ∈ Finset.range 31, stT90 (i+1)) + stT90 32 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 31
    simpa using h
  have hprev := st90_p31
  have hstep := st90_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p33 : ((34904093554691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT90 (i+1))
      = (∑ i ∈ Finset.range 32, stT90 (i+1)) + stT90 33 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 32
    simpa using h
  have hprev := st90_p32
  have hstep := st90_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p34 : ((34088605706789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT90 (i+1))
      = (∑ i ∈ Finset.range 33, stT90 (i+1)) + stT90 34 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 33
    simpa using h
  have hprev := st90_p33
  have hstep := st90_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p35 : ((35536050253349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT90 (i+1))
      = (∑ i ∈ Finset.range 34, stT90 (i+1)) + stT90 35 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 34
    simpa using h
  have hprev := st90_p34
  have hstep := st90_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p36 : ((1693633579367/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT90 (i+1))
      = (∑ i ∈ Finset.range 35, stT90 (i+1)) + stT90 36 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 35
    simpa using h
  have hprev := st90_p35
  have hstep := st90_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p37 : ((701747972391/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT90 (i+1))
      = (∑ i ∈ Finset.range 36, stT90 (i+1)) + stT90 37 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 36
    simpa using h
  have hprev := st90_p36
  have hstep := st90_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p38 : ((1747072072357/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT90 (i+1))
      = (∑ i ∈ Finset.range 37, stT90 (i+1)) + stT90 38 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 37
    simpa using h
  have hprev := st90_p37
  have hstep := st90_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p39 : ((3389304208969/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT90 (i+1))
      = (∑ i ∈ Finset.range 38, stT90 (i+1)) + stT90 39 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 38
    simpa using h
  have hprev := st90_p38
  have hstep := st90_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p40 : ((17737036286153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT90 (i+1))
      = (∑ i ∈ Finset.range 39, stT90 (i+1)) + stT90 40 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 39
    simpa using h
  have hprev := st90_p39
  have hstep := st90_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p41 : ((4316792752651/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT90 (i+1))
      = (∑ i ∈ Finset.range 40, stT90 (i+1)) + stT90 41 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 40
    simpa using h
  have hprev := st90_p40
  have hstep := st90_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p42 : ((17019156841233/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT90 (i+1))
      = (∑ i ∈ Finset.range 41, stT90 (i+1)) + stT90 42 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 41
    simpa using h
  have hprev := st90_p41
  have hstep := st90_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p43 : ((35526557218861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT90 (i+1))
      = (∑ i ∈ Finset.range 42, stT90 (i+1)) + stT90 43 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 42
    simpa using h
  have hprev := st90_p42
  have hstep := st90_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p44 : ((4316837976233/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT90 (i+1))
      = (∑ i ∈ Finset.range 43, stT90 (i+1)) + stT90 44 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 43
    simpa using h
  have hprev := st90_p43
  have hstep := st90_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p45 : ((2122042540723/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT90 (i+1))
      = (∑ i ∈ Finset.range 44, stT90 (i+1)) + stT90 45 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 44
    simpa using h
  have hprev := st90_p44
  have hstep := st90_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p46 : ((17713498221119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT90 (i+1))
      = (∑ i ∈ Finset.range 45, stT90 (i+1)) + stT90 46 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 45
    simpa using h
  have hprev := st90_p45
  have hstep := st90_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p47 : ((17449033306919/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT90 (i+1))
      = (∑ i ∈ Finset.range 46, stT90 (i+1)) + stT90 47 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 46
    simpa using h
  have hprev := st90_p46
  have hstep := st90_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p48 : ((16894716301127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT90 (i+1))
      = (∑ i ∈ Finset.range 47, stT90 (i+1)) + stT90 48 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 47
    simpa using h
  have hprev := st90_p47
  have hstep := st90_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p49 : ((6995152449271/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT90 (i+1))
      = (∑ i ∈ Finset.range 48, stT90 (i+1)) + stT90 49 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 48
    simpa using h
  have hprev := st90_p48
  have hstep := st90_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p50 : ((8862954010157/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT90 (i+1))
      = (∑ i ∈ Finset.range 49, stT90 (i+1)) + stT90 50 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 49
    simpa using h
  have hprev := st90_p49
  have hstep := st90_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p51 : ((34063634868749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT90 (i+1))
      = (∑ i ∈ Finset.range 50, stT90 (i+1)) + stT90 51 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 50
    simpa using h
  have hprev := st90_p50
  have hstep := st90_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p52 : ((34125798710999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT90 (i+1))
      = (∑ i ∈ Finset.range 51, stT90 (i+1)) + stT90 52 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 51
    simpa using h
  have hprev := st90_p51
  have hstep := st90_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p53 : ((8868755212161/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT90 (i+1))
      = (∑ i ∈ Finset.range 52, stT90 (i+1)) + stT90 53 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 52
    simpa using h
  have hprev := st90_p52
  have hstep := st90_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p54 : ((27400696947/7812500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT90 (i+1))
      = (∑ i ∈ Finset.range 53, stT90 (i+1)) + stT90 54 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 53
    simpa using h
  have hprev := st90_p53
  have hstep := st90_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p55 : ((105690287203/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT90 (i+1))
      = (∑ i ∈ Finset.range 54, stT90 (i+1)) + stT90 55 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 54
    simpa using h
  have hprev := st90_p54
  have hstep := st90_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p56 : ((687592429763/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT90 (i+1))
      = (∑ i ∈ Finset.range 55, stT90 (i+1)) + stT90 56 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 55
    simpa using h
  have hprev := st90_p55
  have hstep := st90_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p57 : ((3557015058571/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT90 (i+1))
      = (∑ i ∈ Finset.range 56, stT90 (i+1)) + stT90 57 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 56
    simpa using h
  have hprev := st90_p56
  have hstep := st90_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p58 : ((56002005371/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT90 (i+1))
      = (∑ i ∈ Finset.range 57, stT90 (i+1)) + stT90 58 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 57
    simpa using h
  have hprev := st90_p57
  have hstep := st90_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p59 : ((6762040733539/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT90 (i+1))
      = (∑ i ∈ Finset.range 58, stT90 (i+1)) + stT90 59 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 58
    simpa using h
  have hprev := st90_p58
  have hstep := st90_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p60 : ((6852403858569/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT90 (i+1))
      = (∑ i ∈ Finset.range 59, stT90 (i+1)) + stT90 60 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 59
    simpa using h
  have hprev := st90_p59
  have hstep := st90_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p61 : ((35494409343149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT90 (i+1))
      = (∑ i ∈ Finset.range 60, stT90 (i+1)) + stT90 61 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 60
    simpa using h
  have hprev := st90_p60
  have hstep := st90_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p62 : ((1411325170817/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT90 (i+1))
      = (∑ i ∈ Finset.range 61, stT90 (i+1)) + stT90 62 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 61
    simpa using h
  have hprev := st90_p61
  have hstep := st90_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p63 : ((6804803159689/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT90 (i+1))
      = (∑ i ∈ Finset.range 62, stT90 (i+1)) + stT90 63 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 62
    simpa using h
  have hprev := st90_p62
  have hstep := st90_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p64 : ((16938943465771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT90 (i+1))
      = (∑ i ∈ Finset.range 63, stT90 (i+1)) + stT90 64 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 63
    simpa using h
  have hprev := st90_p63
  have hstep := st90_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p65 : ((701309490631/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT90 (i+1))
      = (∑ i ∈ Finset.range 64, stT90 (i+1)) + stT90 65 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 64
    simpa using h
  have hprev := st90_p64
  have hstep := st90_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p66 : ((8910978563707/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT90 (i+1))
      = (∑ i ∈ Finset.range 65, stT90 (i+1)) + stT90 66 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 65
    simpa using h
  have hprev := st90_p65
  have hstep := st90_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p67 : ((17357352627389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT90 (i+1))
      = (∑ i ∈ Finset.range 66, stT90 (i+1)) + stT90 67 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 66
    simpa using h
  have hprev := st90_p66
  have hstep := st90_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p68 : ((4216552285909/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT90 (i+1))
      = (∑ i ∈ Finset.range 67, stT90 (i+1)) + stT90 68 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 67
    simpa using h
  have hprev := st90_p67
  have hstep := st90_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p69 : ((3416746969517/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT90 (i+1))
      = (∑ i ∈ Finset.range 68, stT90 (i+1)) + stT90 69 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 68
    simpa using h
  have hprev := st90_p68
  have hstep := st90_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p70 : ((17678681098689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT90 (i+1))
      = (∑ i ∈ Finset.range 69, stT90 (i+1)) + stT90 70 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 69
    simpa using h
  have hprev := st90_p69
  have hstep := st90_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p71 : ((35593297820521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT90 (i+1))
      = (∑ i ∈ Finset.range 70, stT90 (i+1)) + stT90 71 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 70
    simpa using h
  have hprev := st90_p70
  have hstep := st90_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p72 : ((1382639179281/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT90 (i+1))
      = (∑ i ∈ Finset.range 71, stT90 (i+1)) + stT90 72 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 71
    simpa using h
  have hprev := st90_p71
  have hstep := st90_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p73 : ((33693117813549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT90 (i+1))
      = (∑ i ∈ Finset.range 72, stT90 (i+1)) + stT90 73 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 72
    simpa using h
  have hprev := st90_p72
  have hstep := st90_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p74 : ((34127363048301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT90 (i+1))
      = (∑ i ∈ Finset.range 73, stT90 (i+1)) + stT90 74 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 73
    simpa using h
  have hprev := st90_p73
  have hstep := st90_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p75 : ((35281770909201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT90 (i+1))
      = (∑ i ∈ Finset.range 74, stT90 (i+1)) + stT90 75 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 74
    simpa using h
  have hprev := st90_p74
  have hstep := st90_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p76 : ((35684254196607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT90 (i+1))
      = (∑ i ∈ Finset.range 75, stT90 (i+1)) + stT90 76 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 75
    simpa using h
  have hprev := st90_p75
  have hstep := st90_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p77 : ((34852592529927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT90 (i+1))
      = (∑ i ∈ Finset.range 76, stT90 (i+1)) + stT90 77 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 76
    simpa using h
  have hprev := st90_p76
  have hstep := st90_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p78 : ((33813395707473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT90 (i+1))
      = (∑ i ∈ Finset.range 77, stT90 (i+1)) + stT90 78 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 77
    simpa using h
  have hprev := st90_p77
  have hstep := st90_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p79 : ((33795510183537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT90 (i+1))
      = (∑ i ∈ Finset.range 78, stT90 (i+1)) + stT90 79 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 78
    simpa using h
  have hprev := st90_p78
  have hstep := st90_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p80 : ((4349994857121/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT90 (i+1))
      = (∑ i ∈ Finset.range 79, stT90 (i+1)) + stT90 80 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 79
    simpa using h
  have hprev := st90_p79
  have hstep := st90_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p81 : ((4459412623957/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT90 (i+1))
      = (∑ i ∈ Finset.range 80, stT90 (i+1)) + stT90 81 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 80
    simpa using h
  have hprev := st90_p80
  have hstep := st90_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p82 : ((4432389459279/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT90 (i+1))
      = (∑ i ∈ Finset.range 81, stT90 (i+1)) + stT90 82 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 81
    simpa using h
  have hprev := st90_p81
  have hstep := st90_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p83 : ((34405045808403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT90 (i+1))
      = (∑ i ∈ Finset.range 82, stT90 (i+1)) + stT90 83 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 82
    simpa using h
  have hprev := st90_p82
  have hstep := st90_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p84 : ((33640893289273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT90 (i+1))
      = (∑ i ∈ Finset.range 83, stT90 (i+1)) + stT90 84 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 83
    simpa using h
  have hprev := st90_p83
  have hstep := st90_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p85 : ((6790048509517/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT90 (i+1))
      = (∑ i ∈ Finset.range 84, stT90 (i+1)) + stT90 85 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 84
    simpa using h
  have hprev := st90_p84
  have hstep := st90_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p86 : ((17500196970701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT90 (i+1))
      = (∑ i ∈ Finset.range 85, stT90 (i+1)) + stT90 86 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 85
    simpa using h
  have hprev := st90_p85
  have hstep := st90_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p87 : ((17869160027053/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT90 (i+1))
      = (∑ i ∈ Finset.range 86, stT90 (i+1)) + stT90 87 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 86
    simpa using h
  have hprev := st90_p86
  have hstep := st90_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p88 : ((17727282889683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT90 (i+1))
      = (∑ i ∈ Finset.range 87, stT90 (i+1)) + stT90 88 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 87
    simpa using h
  have hprev := st90_p87
  have hstep := st90_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p89 : ((4304638849887/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT90 (i+1))
      = (∑ i ∈ Finset.range 88, stT90 (i+1)) + stT90 89 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 88
    simpa using h
  have hprev := st90_p88
  have hstep := st90_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p90 : ((3364537943861/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT90 (i+1))
      = (∑ i ∈ Finset.range 89, stT90 (i+1)) + stT90 90 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 89
    simpa using h
  have hprev := st90_p89
  have hstep := st90_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p91 : ((3379662061271/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT90 (i+1))
      = (∑ i ∈ Finset.range 90, stT90 (i+1)) + stT90 91 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 90
    simpa using h
  have hprev := st90_p90
  have hstep := st90_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p92 : ((17369395943269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT90 (i+1))
      = (∑ i ∈ Finset.range 91, stT90 (i+1)) + stT90 92 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 91
    simpa using h
  have hprev := st90_p91
  have hstep := st90_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p93 : ((285064774369/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT90 (i+1))
      = (∑ i ∈ Finset.range 92, stT90 (i+1)) + stT90 93 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 92
    simpa using h
  have hprev := st90_p92
  have hstep := st90_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p94 : ((8928247408841/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT90 (i+1))
      = (∑ i ∈ Finset.range 93, stT90 (i+1)) + stT90 94 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 93
    simpa using h
  have hprev := st90_p93
  have hstep := st90_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p95 : ((34925584610171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT90 (i+1))
      = (∑ i ∈ Finset.range 94, stT90 (i+1)) + stT90 95 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 94
    simpa using h
  have hprev := st90_p94
  have hstep := st90_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p96 : ((3393574451891/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT90 (i+1))
      = (∑ i ∈ Finset.range 95, stT90 (i+1)) + stT90 96 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 95
    simpa using h
  have hprev := st90_p95
  have hstep := st90_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p97 : ((33548053558553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT90 (i+1))
      = (∑ i ∈ Finset.range 96, stT90 (i+1)) + stT90 97 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 96
    simpa using h
  have hprev := st90_p96
  have hstep := st90_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p98 : ((34059856160721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT90 (i+1))
      = (∑ i ∈ Finset.range 97, stT90 (i+1)) + stT90 98 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 97
    simpa using h
  have hprev := st90_p97
  have hstep := st90_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p99 : ((35056911156867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT90 (i+1))
      = (∑ i ∈ Finset.range 98, stT90 (i+1)) + stT90 99 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 98
    simpa using h
  have hprev := st90_p98
  have hstep := st90_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st90_p100 : ((35768610445167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT90 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT90 (i+1))
      = (∑ i ∈ Finset.range 99, stT90 (i+1)) + stT90 100 := by
    have h := Finset.sum_range_succ (fun i => stT90 (i+1)) 99
    simpa using h
  have hprev := st90_p99
  have hstep := st90_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 90`.** -/
theorem station_90_sign : 0 < hardyG (((90:ℕ)):ℝ) := by
  have hcore := phase_station_lower 90 100 (by norm_num) (by norm_num)
    ((-250931/250000 : ℚ) : ℝ)
  have hchain := st90_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT90 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((90:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-250931/250000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((90:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((90:ℕ)):ℝ)+1) * ((((90:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((1564637/1800000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((35768610445167/10000000000000 : ℚ) : ℝ) - ((1564637/1800000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-250931/250000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((90:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-250931/250000 : ℚ) : ℝ)
        * (riemannZeta (line (((90:ℕ)):ℝ))).re
      - Real.sin ((-250931/250000 : ℚ) : ℝ)
        * (riemannZeta (line (((90:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((90:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((90:ℕ)):ℝ)
      = ((((90:ℕ)):ℝ) * (Real.log (((90:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((90:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_90
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
  have hθwin : |(((-250931/250000 : ℚ) : ℝ) + ((12:ℤ)) * (2*Real.pi)) - theta (((90:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((90:ℕ)):ℝ))
    (φ := ((-250931/250000 : ℚ) : ℝ) + ((12:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-250931/250000 : ℚ)) : ℝ) 12).1,
    (cos_sin_shift (((-250931/250000 : ℚ)) : ℝ) 12).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_90_sign
end AxiomAudit
