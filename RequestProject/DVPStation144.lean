import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 144` (rung-144.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT144 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((144 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))

theorem st144_c1 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((683623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1022601/5000000) (δ := 201/1000000000) (ψ := -818081/1000000) 144 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t1 : ((683573/1000000 : ℚ) : ℝ) ≤ stT144 1 := by
  have hc : ((683573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((683573/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((683573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c2 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((497487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 62691/2500000) (δ := 7287/1000000000) (ψ := -818081/1000000) 144 16
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t2 : ((1758793565977/2500000000000 : ℚ) : ℝ) ≤ stT144 2 := by
  have hc : ((248731/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1758793565977/2500000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((248731/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c3 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-179789/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4846531/10000000) (δ := 7281/1000000000) (ψ := -818081/1000000) 144 25
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t3 : ((-519078334221/2500000000000 : ℚ) : ℝ) ≤ stT144 3 := by
  have hc : ((-89907/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-519078334221/2500000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-89907/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c4 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((16307/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -192957/1250000) (δ := 7231/1000000000) (ψ := -818081/1000000) 144 32
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t4 : ((8153/20000 : ℚ) : ℝ) ≤ stT144 4 := by
  have hc : ((8153/10000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8153/20000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((8153/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c5 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((39803/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7757/312500) (δ := 7367/1000000000) (ψ := -818081/1000000) 144 37
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t5 : ((35599089027/80000000000 : ℚ) : ℝ) ≤ stT144 5 := by
  have hc : ((39801/40000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35599089027/80000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((39801/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c6 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((342853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3052111/10000000) (δ := 1849/250000000) (ψ := -818081/1000000) 144 41
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t6 : ((699743538523/5000000000000 : ℚ) : ℝ) ≤ stT144 6 := by
  have hc : ((342803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((699743538523/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((342803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c7 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-142909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4285491/10000000) (δ := 3689/500000000) (ψ := -818081/1000000) 144 45
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t7 : ((-108066853911/2000000000000 : ℚ) : ℝ) ≤ stT144 7 := by
  have hc : ((-142959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108066853911/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-142959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c8 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((233393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -834519/2500000) (δ := 3673/500000000) (ψ := -818081/1000000) 144 48
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t8 : ((824991876819/10000000000000 : ℚ) : ℝ) ≤ stT144 8 := by
  have hc : ((233343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((824991876819/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((233343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c9 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-249151/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7647877/10000000) (δ := 7243/1000000000) (ψ := -818081/1000000) 144 50
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t9 : ((-830545166109/2500000000000 : ℚ) : ℝ) ≤ stT144 9 := by
  have hc : ((-498327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-830545166109/2500000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-498327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c10 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((814753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1546233/10000000) (δ := 7321/1000000000) (ψ := -818081/1000000) 144 53
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t10 : ((2576316558731/10000000000000 : ℚ) : ℝ) ≤ stT144 10 := by
  have hc : ((814703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2576316558731/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((814703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c11 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((857809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1349513/10000000) (δ := 57/7812500) (ψ := -818081/1000000) 144 55
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t11 : ((2586240311767/10000000000000 : ℚ) : ℝ) ≤ stT144 11 := by
  have hc : ((857759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2586240311767/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((857759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c12 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((109513/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 125769/1000000) (δ := 1823/250000000) (ψ := -818081/1000000) 144 57
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t12 : ((1264474880277/5000000000000 : ℚ) : ℝ) ≤ stT144 12 := by
  have hc : ((438027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1264474880277/5000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((438027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c13 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((859173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83929/625000) (δ := 293/40000000) (ψ := -818081/1000000) 144 59
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t13 : ((4765555281/20000000000 : ℚ) : ℝ) ≤ stT144 13 := by
  have hc : ((859123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4765555281/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((859123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c14 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-189651/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6079911/10000000) (δ := 227/31250000) (ψ := -818081/1000000) 144 61
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t14 : ((-1013794271451/5000000000000 : ℚ) : ℝ) ≤ stT144 14 := by
  have hc : ((-379327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1013794271451/5000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-379327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c15 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((343807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 304957/1000000) (δ := 7247/1000000000) (ψ := -818081/1000000) 144 62
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t15 : ((221894112229/2500000000000 : ℚ) : ℝ) ≤ stT144 15 := by
  have hc : ((343757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((221894112229/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((343757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c16 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-115933/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5132497/10000000) (δ := 3671/500000000) (ψ := -818081/1000000) 144 64
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t16 : ((-579727731891/5000000000000 : ℚ) : ℝ) ≤ stT144 16 := by
  have hc : ((-231891/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-579727731891/5000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-231891/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c17 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((461737/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 246099/2500000) (δ := 1447/200000000) (ψ := -818081/1000000) 144 65
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t17 : ((17497124523/78125000000 : ℚ) : ℝ) ≤ stT144 17 := by
  have hc : ((28857/31250 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17497124523/78125000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((28857/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c18 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-174139/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5853457/10000000) (δ := 291/40000000) (ψ := -818081/1000000) 144 66
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t18 : ((-820958181969/5000000000000 : ℚ) : ℝ) ≤ stT144 18 := by
  have hc : ((-348303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-820958181969/5000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-348303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c19 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-76337/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3049139/5000000) (δ := 7313/1000000000) (ψ := -818081/1000000) 144 68
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t19 : ((-43785152509/250000000000 : ℚ) : ℝ) ≤ stT144 19 := by
  have hc : ((-38171/50000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43785152509/250000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-38171/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c20 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((232391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3340653/10000000) (δ := 3603/500000000) (ψ := -818081/1000000) 144 69
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t20 : ((519530042847/10000000000000 : ℚ) : ℝ) ≤ stT144 20 := by
  have hc : ((232341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((519530042847/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((232341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c21 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((8289/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -92759/625000) (δ := 913/125000000) (ψ := -818081/1000000) 144 70
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t21 : ((18086982353/100000000000 : ℚ) : ℝ) ≤ stT144 21 := by
  have hc : ((16577/20000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18086982353/100000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((16577/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c22 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((492103/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -111227/2500000) (δ := 231/31250000) (ψ := -818081/1000000) 144 71
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t22 : ((524556870273/2500000000000 : ℚ) : ℝ) ≤ stT144 22 := by
  have hc : ((246039/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((524556870273/2500000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((246039/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c23 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((199639/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -150223/10000000) (δ := 1457/200000000) (ψ := -818081/1000000) 144 72
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t23 : ((52031901447/250000000000 : ℚ) : ℝ) ≤ stT144 23 := by
  have hc : ((199629/200000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52031901447/250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((199629/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c24 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((488521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53673/1000000) (δ := 3613/500000000) (ψ := -818081/1000000) 144 73
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t24 : ((62321128971/312500000000 : ℚ) : ℝ) ≤ stT144 24 := by
  have hc : ((30531/31250 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62321128971/312500000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((30531/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c25 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((203541/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1548773/10000000) (δ := 7333/1000000000) (ψ := -818081/1000000) 144 74
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t25 : ((407057/2500000 : ℚ) : ℝ) ≤ stT144 25 := by
  have hc : ((407057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((407057/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((407057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c26 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((62131/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -627457/2000000) (δ := 7363/1000000000) (ψ := -818081/1000000) 144 75
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t26 : ((121829282481/2000000000000 : ℚ) : ℝ) ≤ stT144 26 := by
  have hc : ((62121/200000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121829282481/2000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((62121/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c27 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-507861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -262937/500000) (δ := 907/125000000) (ψ := -818081/1000000) 144 76
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t27 : ((-977475227411/10000000000000 : ℚ) : ℝ) ≤ stT144 27 := by
  have hc : ((-507911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-977475227411/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-507911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c28 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-999967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 244801/312500) (δ := 907/125000000) (ψ := -818081/1000000) 144 76
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t28 : ((-1889855126991/10000000000000 : ℚ) : ℝ) ≤ stT144 28 := by
  have hc : ((-1000017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1889855126991/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-1000017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c29 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-326519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4758537/10000000) (δ := 3627/500000000) (ψ := -818081/1000000) 144 77
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t29 : ((-303211805413/5000000000000 : ℚ) : ℝ) ≤ stT144 29 := by
  have hc : ((-326569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-303211805413/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-326569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c30 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((4383/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 627557/5000000) (δ := 3681/500000000) (ψ := -818081/1000000) 144 78
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t30 : ((32007065471/200000000000 : ℚ) : ℝ) ≤ stT144 30 := by
  have hc : ((17531/20000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32007065471/200000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((17531/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c31 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((2447/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1324243/5000000) (δ := 3667/500000000) (ψ := -818081/1000000) 144 79
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t31 : ((17577970711/200000000000 : ℚ) : ℝ) ≤ stT144 31 := by
  have hc : ((9787/20000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17577970711/200000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((9787/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c32 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-233007/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6926917/10000000) (δ := 7227/1000000000) (ψ := -818081/1000000) 144 80
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t32 : ((-823848364913/5000000000000 : ℚ) : ℝ) ≤ stT144 32 := by
  have hc : ((-466039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-823848364913/5000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-466039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c33 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-22357/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4150859/10000000) (δ := 7227/1000000000) (ψ := -818081/1000000) 144 80
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t33 : ((-77880622203/5000000000000 : ℚ) : ℝ) ≤ stT144 33 := by
  have hc : ((-44739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77880622203/5000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-44739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c34 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((947967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -101253/1250000) (δ := 7283/1000000000) (ψ := -818081/1000000) 144 81
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t34 : ((325132687249/2000000000000 : ℚ) : ℝ) ≤ stT144 34 := by
  have hc : ((947917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((325132687249/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((947917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c35 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-30371/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6082487/10000000) (δ := 739/100000000) (ψ := -818081/1000000) 144 82
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t35 : ((-51339755257/400000000000 : ℚ) : ℝ) ≤ stT144 35 := by
  have hc : ((-30373/40000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51339755257/400000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-30373/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c36 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-26397/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4059037/10000000) (δ := 739/100000000) (ψ := -818081/1000000) 144 82
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t36 : ((-22018337737/2500000000000 : ℚ) : ℝ) ≤ stT144 36 := by
  have hc : ((-13211/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22018337737/2500000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-13211/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c37 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((755673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1785287/10000000) (δ := 3653/500000000) (ψ := -818081/1000000) 144 83
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t37 : ((1242235900147/10000000000000 : ℚ) : ℝ) ≤ stT144 37 := by
  have hc : ((755623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1242235900147/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((755623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c38 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-24997/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1563053/2000000) (δ := 3653/500000000) (ψ := -818081/1000000) 144 83
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t38 : ((-32442028899/200000000000 : ℚ) : ℝ) ≤ stT144 38 := by
  have hc : ((-99993/100000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32442028899/200000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-99993/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c39 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((834599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 729241/5000000) (δ := 1441/200000000) (ψ := -818081/1000000) 144 84
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t39 : ((1336347457269/10000000000000 : ℚ) : ℝ) ≤ stT144 39 := by
  have hc : ((834549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1336347457269/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((834549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c40 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-116161/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5135073/10000000) (δ := 457/62500000) (ψ := -818081/1000000) 144 85
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t40 : ((-367372903233/5000000000000 : ℚ) : ℝ) ≤ stT144 40 := by
  have hc : ((-232347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-367372903233/5000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-232347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c41 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((17259/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3754263/10000000) (δ := 457/62500000) (ψ := -818081/1000000) 144 85
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t41 : ((53868994341/5000000000000 : ℚ) : ℝ) ≤ stT144 41 := by
  have hc : ((34493/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53868994341/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((34493/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c42 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((32059/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -655713/2000000) (δ := 923/125000000) (ψ := -818081/1000000) 144 86
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t42 : ((197833803963/5000000000000 : ℚ) : ℝ) ≤ stT144 42 := by
  have hc : ((128211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197833803963/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((128211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c43 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-484831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1038483/2000000) (δ := 923/125000000) (ψ := -818081/1000000) 144 86
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t43 : ((-369718368333/5000000000000 : ℚ) : ℝ) ≤ stT144 43 := by
  have hc : ((-484881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-369718368333/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-484881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c44 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((156237/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -69979/312500) (δ := 7277/1000000000) (ψ := -818081/1000000) 144 87
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t44 : ((117758591161/1250000000000 : ℚ) : ℝ) ≤ stT144 44 := by
  have hc : ((312449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117758591161/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((312449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c45 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-86977/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9142/15625) (δ := 7277/1000000000) (ψ := -818081/1000000) 144 87
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t45 : ((-64833487287/625000000000 : ℚ) : ℝ) ≤ stT144 45 := by
  have hc : ((-347933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64833487287/625000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-347933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c46 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((712409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1944679/10000000) (δ := 7233/1000000000) (ψ := -818081/1000000) 144 88
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t46 : ((1050315644421/10000000000000 : ℚ) : ℝ) ≤ stT144 46 := by
  have hc : ((712359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1050315644421/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((712359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c47 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-680349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5797589/10000000) (δ := 7233/1000000000) (ψ := -818081/1000000) 144 88
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t47 : ((-19849280027/200000000000 : ℚ) : ℝ) ≤ stT144 47 := by
  have hc : ((-680399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19849280027/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-680399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c48 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((29793/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46623/200000) (δ := 367/50000000) (ψ := -818081/1000000) 144 89
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t48 : ((687981807/8000000000 : ℚ) : ℝ) ≤ stT144 48 := by
  have hc : ((59581/100000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((687981807/8000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((59581/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c49 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-89847/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2545881/5000000) (δ := 367/50000000) (ψ := -818081/1000000) 144 89
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t49 : ((-32091798551/500000000000 : ℚ) : ℝ) ≤ stT144 49 := by
  have hc : ((-89857/200000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32091798551/500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-89857/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c50 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((115701/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1671597/5000000) (δ := 1471/200000000) (ψ := -818081/1000000) 144 90
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t50 : ((40897625747/1250000000000 : ℚ) : ℝ) ≤ stT144 50 := by
  have hc : ((28919/125000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40897625747/1250000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((28919/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c51 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((56469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1892871/5000000) (δ := 1471/200000000) (ψ := -818081/1000000) 144 90
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t51 : ((1975059933/250000000000 : ℚ) : ℝ) ≤ stT144 51 := by
  have hc : ((56419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1975059933/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((56419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c52 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-195577/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -986341/2000000) (δ := 453/62500000) (ψ := -818081/1000000) 144 91
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t52 : ((-135625634551/2500000000000 : ℚ) : ℝ) ≤ stT144 52 := by
  have hc : ((-97801/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135625634551/2500000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-97801/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c53 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((71773/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1925647/10000000) (δ := 453/62500000) (ψ := -818081/1000000) 144 91
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t53 : ((2464522091/25000000000 : ℚ) : ℝ) ≤ stT144 53 := by
  have hc : ((8971/12500 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2464522091/25000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((8971/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c54 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-237283/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -176329/250000) (δ := 3631/500000000) (ψ := -818081/1000000) 144 92
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t54 : ((-161459180337/1250000000000 : ℚ) : ℝ) ≤ stT144 54 := by
  have hc : ((-474591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161459180337/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-474591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c55 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((984023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -111871/2500000) (δ := 3631/500000000) (ψ := -818081/1000000) 144 92
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t55 : ((1326788209227/10000000000000 : ℚ) : ℝ) ≤ stT144 55 := by
  have hc : ((983973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1326788209227/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((983973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c56 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-46743/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 754897/1250000) (δ := 3631/500000000) (ψ := -818081/1000000) 144 92
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t56 : ((-499737392483/5000000000000 : ℚ) : ℝ) ≤ stT144 56 := by
  have hc : ((-373969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-499737392483/5000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-373969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c57 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((62341/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3296931/10000000) (δ := 7369/1000000000) (ψ := -818081/1000000) 144 93
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t57 : ((41278046381/1250000000000 : ℚ) : ℝ) ≤ stT144 57 := by
  have hc : ((124657/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41278046381/1250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((124657/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c58 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((187849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2964117/10000000) (δ := 7369/1000000000) (ψ := -818081/1000000) 144 93
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t58 : ((1926757287/39062500000 : ℚ) : ℝ) ≤ stT144 58 := by
  have hc : ((11739/31250 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1926757287/39062500000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((11739/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c59 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-874861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6589863/10000000) (δ := 7327/1000000000) (ψ := -818081/1000000) 144 94
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t59 : ((-113903788179/1000000000000 : ℚ) : ℝ) ≤ stT144 59 := by
  have hc : ((-874911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113903788179/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-874911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c60 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((488411/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -539307/10000000) (δ := 7327/1000000000) (ψ := -818081/1000000) 144 94
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t60 : ((157625848921/1250000000000 : ℚ) : ℝ) ≤ stT144 60 := by
  have hc : ((244193/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157625848921/1250000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((244193/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c61 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-69929/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5411241/10000000) (δ := 7327/1000000000) (ψ := -818081/1000000) 144 94
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t61 : ((-358171704429/5000000000000 : ℚ) : ℝ) ≤ stT144 61 := by
  have hc : ((-279741/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-358171704429/5000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-279741/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c62 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-204919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2221471/5000000) (δ := 7219/1000000000) (ψ := -818081/1000000) 144 95
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t62 : ((-130155519969/5000000000000 : ℚ) : ℝ) ≤ stT144 62 := by
  have hc : ((-204969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130155519969/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-204969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c63 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((43219/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 658601/5000000) (δ := 7219/1000000000) (ψ := -818081/1000000) 144 95
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t63 : ((108895294473/1000000000000 : ℚ) : ℝ) ≤ stT144 63 := by
  have hc : ((86433/100000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108895294473/1000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((86433/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c64 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-235103/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 698659/1000000) (δ := 7219/1000000000) (ψ := -818081/1000000) 144 95
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t64 : ((-587789220231/5000000000000 : ℚ) : ℝ) ≤ stT144 64 := by
  have hc : ((-470231/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-587789220231/5000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-470231/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c65 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((77419/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3139861/10000000) (δ := 7291/1000000000) (ψ := -818081/1000000) 144 96
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t65 : ((192021840111/5000000000000 : ℚ) : ℝ) ≤ stT144 65 := by
  have hc : ((154813/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192021840111/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((154813/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c66 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((293853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2356439/10000000) (δ := 7291/1000000000) (ψ := -818081/1000000) 144 96
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t66 : ((45209624849/625000000000 : ℚ) : ℝ) ≤ stT144 66 := by
  have hc : ((73457/125000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45209624849/625000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((73457/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c67 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-999437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7770083/10000000) (δ := 7291/1000000000) (ψ := -818081/1000000) 144 96
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t67 : ((-244213654093/2000000000000 : ℚ) : ℝ) ≤ stT144 67 := by
  have hc : ((-999487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244213654093/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-999487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c68 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((252343/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -651111/2500000) (δ := 3699/500000000) (ψ := -818081/1000000) 144 97
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t68 : ((76495121901/1250000000000 : ℚ) : ℝ) ≤ stT144 68 := by
  have hc : ((126159/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76495121901/1250000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((126159/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c69 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((3053/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 662781/2500000) (δ := 3699/500000000) (ψ := -818081/1000000) 144 97
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t69 : ((29400018147/500000000000 : ℚ) : ℝ) ≤ stT144 69 := by
  have hc : ((48843/100000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29400018147/500000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((48843/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c70 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-499979/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 489441/625000) (δ := 3699/500000000) (ψ := -818081/1000000) 144 97
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t70 : ((-149404820229/1250000000000 : ℚ) : ℝ) ≤ stT144 70 := by
  have hc : ((-125001/125000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149404820229/1250000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-125001/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c71 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((44629/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -692613/2500000) (δ := 3649/500000000) (ψ := -818081/1000000) 144 98
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t71 : ((3309932209/62500000000 : ℚ) : ℝ) ≤ stT144 71 := by
  have hc : ((2789/6250 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3309932209/62500000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((2789/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c72 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((30851/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 283077/1250000) (δ := 3649/500000000) (ψ := -818081/1000000) 144 98
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t72 : ((72710593167/1000000000000 : ℚ) : ℝ) ≤ stT144 72 := by
  have hc : ((61697/100000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72710593167/1000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((61697/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c73 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-969033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1807551/2500000) (δ := 3649/500000000) (ψ := -818081/1000000) 144 98
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t73 : ((-283556593049/2500000000000 : ℚ) : ℝ) ≤ stT144 73 := by
  have hc : ((-969083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-283556593049/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-969083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c74 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((138453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3579743/10000000) (δ := 1803/250000000) (ψ := -818081/1000000) 144 99
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t74 : ((40222541457/2500000000000 : ℚ) : ℝ) ≤ stT144 74 := by
  have hc : ((138403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40222541457/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((138403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c75 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((877089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1252573/10000000) (δ := 1803/250000000) (ψ := -818081/1000000) 144 99
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t75 : ((10127169333/100000000000 : ℚ) : ℝ) ≤ stT144 75 := by
  have hc : ((877039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10127169333/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((877039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c76 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-743/1000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1204169/2000000) (δ := 1803/250000000) (ψ := -818081/1000000) 144 99
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t76 : ((-17046741019/200000000000 : ℚ) : ℝ) ≤ stT144 76 := by
  have hc : ((-14861/20000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17046741019/200000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-14861/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c77 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-409283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2490581/5000000) (δ := 7319/1000000000) (ψ := -818081/1000000) 144 100
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t77 : ((-233239171399/5000000000000 : ℚ) : ℝ) ≤ stT144 77 := by
  have hc : ((-409333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233239171399/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-409333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c78 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((198197/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -167969/5000000) (δ := 7319/1000000000) (ψ := -818081/1000000) 144 100
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t78 : ((224402581799/2000000000000 : ℚ) : ℝ) ≤ stT144 78 := by
  have hc : ((198187/200000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224402581799/2000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((198187/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c79 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-25777/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2125051/5000000) (δ := 7319/1000000000) (ψ := -818081/1000000) 144 100
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t79 : ((-906645133/62500000000 : ℚ) : ℝ) ≤ stT144 79 := by
  have hc : ((-25787/200000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-906645133/62500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-25787/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c80 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-932401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3464747/5000000) (δ := 461/62500000) (ψ := -818081/1000000) 144 101
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t80 : ((-521255960667/5000000000000 : ℚ) : ℝ) ≤ stT144 80 := by
  have hc : ((-932451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-521255960667/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-932451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c81 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((138641/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1228697/5000000) (δ := 461/62500000) (ψ := -818081/1000000) 144 101
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t81 : ((308063302527/5000000000000 : ℚ) : ℝ) ≤ stT144 81 := by
  have hc : ((277257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((308063302527/5000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((277257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c82 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((708139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 979921/5000000) (δ := 461/62500000) (ψ := -818081/1000000) 144 101
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t82 : ((156390660807/2000000000000 : ℚ) : ℝ) ≤ stT144 82 := by
  have hc : ((708089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156390660807/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((708089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c83 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-818401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3161773/5000000) (δ := 461/62500000) (ψ := -818081/1000000) 144 101
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t83 : ((-898367010993/10000000000000 : ℚ) : ℝ) ≤ stT144 83 := by
  have hc : ((-818451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-898367010993/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-818451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c84 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-221259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5073003/10000000) (δ := 14469/1000000000) (ψ := -818081/1000000) 144 102
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t84 : ((-6036018989/125000000000 : ℚ) : ℝ) ≤ stT144 84 := by
  have hc : ((-55321/125000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6036018989/125000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-55321/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c85 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((473819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -812601/10000000) (δ := 7269/1000000000) (ψ := -818081/1000000) 144 102
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t85 : ((64237701211/625000000000 : ℚ) : ℝ) ≤ stT144 85 := by
  have hc : ((236897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64237701211/625000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((236897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c86 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((210037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3397959/10000000) (δ := 7269/1000000000) (ψ := -818081/1000000) 144 102
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t86 : ((226434651749/10000000000000 : ℚ) : ℝ) ≤ stT144 86 := by
  have hc : ((209987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226434651749/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((209987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c87 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-15517/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7559883/10000000) (δ := 7269/1000000000) (ψ := -818081/1000000) 144 102
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t87 : ((-532378080297/5000000000000 : ℚ) : ℝ) ≤ stT144 87 := by
  have hc : ((-496569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-532378080297/5000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-496569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c88 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-4269/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1008437/2500000) (δ := 7241/1000000000) (ψ := -818081/1000000) 144 103
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t88 : ((-569512637/125000000000 : ℚ) : ℝ) ≤ stT144 88 := by
  have hc : ((-2137/50000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-569512637/125000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-2137/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c89 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((999907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4259/1250000) (δ := 7241/1000000000) (ψ := -818081/1000000) 144 103
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t89 : ((1059845420429/10000000000000 : ℚ) : ℝ) ≤ stT144 89 := by
  have hc : ((999857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1059845420429/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((999857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c90 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-10353/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 202823/500000) (δ := 7241/1000000000) (ψ := -818081/1000000) 144 103
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t90 : ((-10923565759/2000000000000 : ℚ) : ℝ) ≤ stT144 90 := by
  have hc : ((-10363/200000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10923565759/2000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-10363/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c91 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-997397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7673557/10000000) (δ := 3637/250000000) (ψ := -818081/1000000) 144 104
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t91 : ((-209121745679/2000000000000 : ℚ) : ℝ) ≤ stT144 91 := by
  have hc : ((-997447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209121745679/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-997447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c92 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((37543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3739099/10000000) (δ := 1837/250000000) (ψ := -818081/1000000) 144 104
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t92 : ((4889402037/625000000000 : ℚ) : ℝ) ≤ stT144 92 := by
  have hc : ((18759/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4889402037/625000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((18759/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c93 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((249533/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6113/400000) (δ := 1837/250000000) (ψ := -818081/1000000) 144 104
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t93 : ((517481063991/5000000000000 : ℚ) : ℝ) ≤ stT144 93 := by
  have hc : ((499041/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((517481063991/5000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((499041/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c94 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-7613/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4003133/10000000) (δ := 1837/250000000) (ψ := -818081/1000000) 144 104
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t94 : ((-7865108461/2500000000000 : ℚ) : ℝ) ≤ stT144 94 := by
  have hc : ((-15251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7865108461/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-15251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c95 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-124983/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7812689/10000000) (δ := 1837/250000000) (ψ := -818081/1000000) 144 104
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t95 : ((-512945382903/5000000000000 : ℚ) : ℝ) ≤ stT144 95 := by
  have hc : ((-499957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512945382903/5000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-499957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c96 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-79363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4125607/10000000) (δ := 1837/250000000) (ψ := -818081/1000000) 144 105
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t96 : ((-81050575473/10000000000000 : ℚ) : ℝ) ≤ stT144 96 := by
  have hc : ((-79413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81050575473/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-79413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c97 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((123443/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -394999/10000000) (δ := 1837/250000000) (ψ := -818081/1000000) 144 105
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t97 : ((250662020731/2500000000000 : ℚ) : ℝ) ≤ stT144 97 := by
  have hc : ((493747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250662020731/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((493747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c98 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((124603/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3297341/10000000) (δ := 1837/250000000) (ψ := -818081/1000000) 144 105
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t98 : ((7865169741/312500000000 : ℚ) : ℝ) ≤ stT144 98 := by
  have hc : ((62289/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7865169741/312500000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((62289/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c99 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-467823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1390441/2000000) (δ := 1837/250000000) (ψ := -818081/1000000) 144 105
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t99 : ((-29387813639/312500000000 : ℚ) : ℝ) ≤ stT144 99 := by
  have hc : ((-58481/62500 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29387813639/312500000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-58481/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c100 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-465557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -102753/200000) (δ := 181/25000000) (ψ := -818081/1000000) 144 106
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t100 : ((-465607/10000000 : ℚ) : ℝ) ≤ stT144 100 := by
  have hc : ((-465607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-465607/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-465607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c101 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((812597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -777753/5000000) (δ := 181/25000000) (ψ := -818081/1000000) 144 106
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t101 : ((808514329239/10000000000000 : ℚ) : ℝ) ≤ stT144 101 := by
  have hc : ((812547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((808514329239/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((812547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c102 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((699193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 995661/5000000) (δ := 181/25000000) (ψ := -818081/1000000) 144 106
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t102 : ((692254344021/10000000000000 : ℚ) : ℝ) ≤ stT144 102 := by
  have hc : ((699143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((692254344021/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((699143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c103 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-294819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2751759/5000000) (δ := 181/25000000) (ψ := -818081/1000000) 144 106
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t103 : ((-7262965963/125000000000 : ℚ) : ℝ) ≤ stT144 103 := by
  have hc : ((-73711/125000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7262965963/125000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-73711/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c104 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-224989/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6726161/10000000) (δ := 727/100000000) (ψ := -818081/1000000) 144 107
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t104 : ((-441264391743/5000000000000 : ℚ) : ℝ) ≤ stT144 104 := by
  have hc : ((-450003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-441264391743/5000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-450003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c105 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((63869/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3281141/10000000) (δ := 727/100000000) (ψ := -818081/1000000) 144 107
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t105 : ((1246351167/50000000000 : ℚ) : ℝ) ≤ stT144 105 := by
  have hc : ((127713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1246351167/50000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((127713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c106 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((998623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 131191/10000000) (δ := 727/100000000) (ψ := -818081/1000000) 144 107
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t106 : ((193979795261/2000000000000 : ℚ) : ℝ) ≤ stT144 106 := by
  have hc : ((998573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193979795261/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((998573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c107 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((6617/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3511519/10000000) (δ := 727/100000000) (ψ := -818081/1000000) 144 107
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t107 : ((79936983/5000000000 : ℚ) : ℝ) ≤ stT144 107 := by
  have hc : ((1323/8000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79936983/5000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((1323/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c108 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-184411/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6860383/10000000) (δ := 727/100000000) (ψ := -818081/1000000) 144 107
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t108 : ((-177459291671/2000000000000 : ℚ) : ℝ) ≤ stT144 108 := by
  have hc : ((-184421/200000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177459291671/2000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-184421/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c109 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-299017/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1382401/2500000) (δ := 7377/1000000000) (ψ := -818081/1000000) 144 108
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t109 : ((-143215250867/2500000000000 : ℚ) : ℝ) ≤ stT144 109 := by
  have hc : ((-149521/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143215250867/2500000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-149521/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c110 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((624143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -140119/625000) (δ := 7377/1000000000) (ψ := -818081/1000000) 144 108
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t110 : ((297524479983/5000000000000 : ℚ) : ℝ) ≤ stT144 110 := by
  have hc : ((624093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((297524479983/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((624093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c111 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((45927/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50803/500000) (δ := 7377/1000000000) (ψ := -818081/1000000) 144 108
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t111 : ((87179121293/1000000000000 : ℚ) : ℝ) ≤ stT144 111 := by
  have hc : ((91849/100000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87179121293/1000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((91849/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c112 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-31691/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1061189/2500000) (δ := 7377/1000000000) (ψ := -818081/1000000) 144 108
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t112 : ((-3744627199/312500000000 : ℚ) : ℝ) ≤ stT144 112 := by
  have hc : ((-63407/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3744627199/312500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-63407/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c113 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-197327/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1861199/2500000) (δ := 7377/1000000000) (ψ := -818081/1000000) 144 108
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t113 : ((-185639059977/2000000000000 : ℚ) : ℝ) ≤ stT144 113 := by
  have hc : ((-197337/200000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185639059977/2000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-197337/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c114 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-7017/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -636419/1250000) (δ := 7319/1000000000) (ψ := -818081/1000000) 144 109
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t114 : ((-105164090717/2500000000000 : ℚ) : ℝ) ≤ stT144 114 := by
  have hc : ((-224569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105164090717/2500000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-224569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c115 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((142339/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -97361/500000) (δ := 7319/1000000000) (ψ := -818081/1000000) 144 109
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t115 : ((16590295227/250000000000 : ℚ) : ℝ) ≤ stT144 115 := by
  have hc : ((142329/200000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16590295227/250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((142329/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c116 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((446267/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58483/500000) (δ := 7319/1000000000) (ψ := -818081/1000000) 144 109
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t116 : ((51790623399/625000000000 : ℚ) : ℝ) ≤ stT144 116 := by
  have hc : ((223121/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51790623399/625000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((223121/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c117 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-66371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1064957/2500000) (δ := 7319/1000000000) (ψ := -818081/1000000) 144 109
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t117 : ((-15345792099/1250000000000 : ℚ) : ℝ) ≤ stT144 117 := by
  have hc : ((-16599/125000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15345792099/1250000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-16599/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c118 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-977587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45773/62500) (δ := 7319/1000000000) (ψ := -818081/1000000) 144 109
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t118 : ((-35999527251/400000000000 : ℚ) : ℝ) ≤ stT144 118 := by
  have hc : ((-977637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35999527251/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-977637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c119 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-537719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1069263/2000000) (δ := 1803/250000000) (ψ := -818081/1000000) 144 110
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t119 : ((-492972304531/10000000000000 : ℚ) : ℝ) ≤ stT144 119 := by
  have hc : ((-537769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-492972304531/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-537769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c120 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((74379/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2333727/10000000) (δ := 1803/250000000) (ψ := -818081/1000000) 144 110
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t120 : ((27157060917/500000000000 : ℚ) : ℝ) ≤ stT144 120 := by
  have hc : ((297491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27157060917/500000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((297491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c121 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((482997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 653841/10000000) (δ := 1803/250000000) (ψ := -818081/1000000) 144 110
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t121 : ((10976625387/125000000000 : ℚ) : ℝ) ≤ stT144 121 := by
  have hc : ((120743/125000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10976625387/125000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((120743/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c122 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((99/800 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3616821/10000000) (δ := 1803/250000000) (ψ := -818081/1000000) 144 110
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t122 : ((1119926609/100000000000 : ℚ) : ℝ) ≤ stT144 122 := by
  have hc : ((1237/10000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1119926609/100000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((1237/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c123 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-434071/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6555609/10000000) (δ := 1803/250000000) (ψ := -818081/1000000) 144 110
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t123 : ((-2446320877/31250000000 : ℚ) : ℝ) ≤ stT144 123 := by
  have hc : ((-27131/31250 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2446320877/31250000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-27131/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c124 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-199527/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3118681/5000000) (δ := 3649/500000000) (ψ := -818081/1000000) 144 111
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t124 : ((-358383717133/5000000000000 : ℚ) : ℝ) ≤ stT144 124 := by
  have hc : ((-399079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-358383717133/5000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-399079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c125 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((144/625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -334577/1000000) (δ := 3649/500000000) (ψ := -818081/1000000) 144 111
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t125 : ((4120625189/200000000000 : ℚ) : ℝ) ≤ stT144 125 := by
  have hc : ((4607/20000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4120625189/200000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((4607/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c126 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((245459/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -238609/5000000) (δ := 3649/500000000) (ψ := -818081/1000000) 144 111
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t126 : ((43732184691/500000000000 : ℚ) : ℝ) ≤ stT144 126 := by
  have hc : ((490893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43732184691/500000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((490893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c127 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((291879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1184309/5000000) (δ := 3649/500000000) (ψ := -818081/1000000) 144 111
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t127 : ((32372299753/625000000000 : ℚ) : ℝ) ≤ stT144 127 := by
  have hc : ((145927/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32372299753/625000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((145927/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c128 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-96949/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 519217/1000000) (δ := 3649/500000000) (ψ := -818081/1000000) 144 111
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t128 : ((-21425127189/500000000000 : ℚ) : ℝ) ≤ stT144 128 := by
  have hc : ((-96959/200000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21425127189/500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-96959/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c129 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-998437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3857101/5000000) (δ := 7397/1000000000) (ψ := -818081/1000000) 144 112
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t129 : ((-879118877637/10000000000000 : ℚ) : ℝ) ≤ stT144 129 := by
  have hc : ((-998487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-879118877637/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-998487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c130 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-392103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2467141/5000000) (δ := 7397/1000000000) (ψ := -818081/1000000) 144 112
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t130 : ((-343941318027/10000000000000 : ℚ) : ℝ) ≤ stT144 130 := by
  have hc : ((-392153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-343941318027/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-392153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c131 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((644631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1087819/5000000) (δ := 7397/1000000000) (ψ := -818081/1000000) 144 112
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t131 : ((70396624753/1250000000000 : ℚ) : ℝ) ≤ stT144 131 := by
  have hc : ((644581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70396624753/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((644581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c132 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((974837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 281009/5000000) (δ := 7397/1000000000) (ψ := -818081/1000000) 144 112
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t132 : ((212110726839/2500000000000 : ℚ) : ℝ) ≤ stT144 132 := by
  have hc : ((974787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212110726839/2500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((974787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c133 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((2563/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 327901/1000000) (δ := 7397/1000000000) (ψ := -818081/1000000) 144 112
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t133 : ((35551469/1600000000 : ℚ) : ℝ) ≤ stT144 133 := by
  have hc : ((41/160 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35551469/1600000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((41/160 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c134 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-365389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1493911/2500000) (δ := 14597/1000000000) (ψ := -818081/1000000) 144 112
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t134 : ((-157834913383/2500000000000 : ℚ) : ℝ) ≤ stT144 134 := by
  have hc : ((-182707/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157834913383/2500000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-182707/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c135 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-59341/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7055737/10000000) (δ := 729/100000000) (ψ := -818081/1000000) 144 113
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t135 : ((-408602341239/5000000000000 : ℚ) : ℝ) ≤ stT144 135 := by
  have hc : ((-474753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-408602341239/5000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-474753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c136 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-37529/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4398901/10000000) (δ := 729/100000000) (ψ := -818081/1000000) 144 113
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t136 : ((-32189429727/2000000000000 : ℚ) : ℝ) ≤ stT144 136 := by
  have hc : ((-37539/200000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32189429727/2000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-37539/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c137 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((761869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -352301/2000000) (δ := 729/100000000) (ψ := -818081/1000000) 144 113
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t137 : ((650865395383/10000000000000 : ℚ) : ℝ) ≤ stT144 137 := by
  have hc : ((761819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((650865395383/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((761819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c138 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((470931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 856667/10000000) (δ := 729/100000000) (ψ := -818081/1000000) 144 113
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t138 : ((25053847371/312500000000 : ℚ) : ℝ) ≤ stT144 138 := by
  have hc : ((235453/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25053847371/312500000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((235453/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c139 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((93647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 138239/400000) (δ := 729/100000000) (ψ := -818081/1000000) 144 113
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t139 : ((9926132117/625000000000 : ℚ) : ℝ) ≤ stT144 139 := by
  have hc : ((46811/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9926132117/625000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((46811/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c140 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-186803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1207327/2000000) (δ := 729/100000000) (ψ := -818081/1000000) 144 113
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t140 : ((-63155221561/1000000000000 : ℚ) : ℝ) ≤ stT144 140 := by
  have hc : ((-373631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63155221561/1000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-373631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c141 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-191187/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -888633/1250000) (δ := 361/50000000) (ψ := -818081/1000000) 144 114
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t141 : ((-20127116993/250000000000 : ℚ) : ℝ) ≤ stT144 141 := by
  have hc : ((-191197/200000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20127116993/250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-191197/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c142 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-252393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -570609/1250000) (δ := 361/50000000) (ψ := -818081/1000000) 144 114
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t142 : ((-105922810813/5000000000000 : ℚ) : ℝ) ≤ stT144 142 := by
  have hc : ((-252443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105922810813/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-252443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c143 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((685567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -254817/1250000) (δ := 361/50000000) (ψ := -818081/1000000) 144 114
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t143 : ((286629053557/5000000000000 : ℚ) : ℝ) ≤ stT144 143 := by
  have hc : ((685517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((286629053557/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((685517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c144 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((30699/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5877/125000) (δ := 361/50000000) (ψ := -818081/1000000) 144 114
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t144 : ((409299002947/5000000000000 : ℚ) : ℝ) ≤ stT144 144 := by
  have hc : ((491159/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((409299002947/5000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((491159/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c145 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((376653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 148077/500000) (δ := 361/50000000) (ψ := -818081/1000000) 144 114
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t145 : ((156375733881/5000000000000 : ℚ) : ℝ) ≤ stT144 145 := by
  have hc : ((376603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156375733881/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((376603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c146 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-283771/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 679473/1250000) (δ := 361/50000000) (ψ := -818081/1000000) 144 114
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t146 : ((-29358909047/625000000000 : ℚ) : ℝ) ≤ stT144 146 := by
  have hc : ((-70949/125000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29358909047/625000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-70949/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c147 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-499939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1562971/2000000) (δ := 7327/1000000000) (ψ := -818081/1000000) 144 115
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t147 : ((-103090951917/1250000000000 : ℚ) : ℝ) ≤ stT144 147 := by
  have hc : ((-124991/125000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103090951917/1250000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-124991/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c148 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-547077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5374163/10000000) (δ := 7327/1000000000) (ψ := -818081/1000000) 144 115
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t148 : ((-89947131673/2000000000000 : ℚ) : ℝ) ≤ stT144 148 := by
  have hc : ((-547127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89947131673/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-547127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c149 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((380967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2949887/10000000) (δ := 7327/1000000000) (ψ := -818081/1000000) 144 115
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t149 : ((312059014827/10000000000000 : ℚ) : ℝ) ≤ stT144 149 := by
  have hc : ((380917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((312059014827/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((380917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c150 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((976601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -541883/10000000) (δ := 7327/1000000000) (ψ := -818081/1000000) 144 115
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t150 : ((49834374081/625000000000 : ℚ) : ℝ) ≤ stT144 150 := by
  have hc : ((976551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49834374081/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((976551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c151 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((369211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1850173/10000000) (δ := 7327/1000000000) (ψ := -818081/1000000) 144 115
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t151 : ((37554892071/625000000000 : ℚ) : ℝ) ≤ stT144 151 := by
  have hc : ((184593/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37554892071/625000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((184593/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c152 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-1867/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 169057/400000) (δ := 7327/1000000000) (ψ := -818081/1000000) 144 115
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t152 : ((-12119778513/1250000000000 : ℚ) : ℝ) ≤ stT144 152 := by
  have hc : ((-59769/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12119778513/1250000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-59769/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c153 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-874323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6587089/10000000) (δ := 7327/1000000000) (ψ := -818081/1000000) 144 115
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t153 : ((-706889474969/10000000000000 : ℚ) : ℝ) ≤ stT144 153 := by
  have hc : ((-874373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-706889474969/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-874373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c154 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-454199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6775583/10000000) (δ := 7369/1000000000) (ψ := -818081/1000000) 144 116
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t154 : ((-22876509147/312500000000 : ℚ) : ℝ) ≤ stT144 154 := by
  have hc : ((-28389/31250 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22876509147/312500000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-28389/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c155 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-205913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4445483/10000000) (δ := 7369/1000000000) (ψ := -818081/1000000) 144 116
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t155 : ((-8271680043/500000000000 : ℚ) : ℝ) ≤ stT144 155 := by
  have hc : ((-205963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8271680043/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-205963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c156 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((658371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2130359/10000000) (δ := 7369/1000000000) (ψ := -818081/1000000) 144 116
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t156 : ((823559571/15625000000 : ℚ) : ℝ) ≤ stT144 156 := by
  have hc : ((658321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((823559571/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((658321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c157 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((99769/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 169969/10000000) (δ := 7369/1000000000) (ψ := -818081/1000000) 144 116
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t157 : ((9952531463/125000000000 : ℚ) : ℝ) ≤ stT144 157 := by
  have hc : ((24941/25000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9952531463/125000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((24941/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c158 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((277567/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2455681/10000000) (δ := 7369/1000000000) (ψ := -818081/1000000) 144 116
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t158 : ((110400240447/2500000000000 : ℚ) : ℝ) ≤ stT144 158 := by
  have hc : ((138771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110400240447/2500000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((138771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c159 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-314567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4726993/10000000) (δ := 7369/1000000000) (ψ := -818081/1000000) 144 116
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t159 : ((-62376910271/2500000000000 : ℚ) : ℝ) ≤ stT144 159 := by
  have hc : ((-314617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62376910271/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-314617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c160 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-470033/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6984049/10000000) (δ := 7369/1000000000) (ψ := -818081/1000000) 144 116
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t160 : ((-18580687653/250000000000 : ℚ) : ℝ) ≤ stT144 160 := by
  have hc : ((-235029/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18580687653/250000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-235029/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c161 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-213233/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3240467/5000000) (δ := 7261/1000000000) (ψ := -818081/1000000) 144 117
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t161 : ((-336122248501/5000000000000 : ℚ) : ℝ) ≤ stT144 161 := by
  have hc : ((-426491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-336122248501/5000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-426491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c162 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-32391/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2125907/5000000) (δ := 7261/1000000000) (ψ := -818081/1000000) 144 117
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t162 : ((-2036689589/200000000000 : ℚ) : ℝ) ≤ stT144 162 := by
  have hc : ((-64807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2036689589/200000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-64807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c163 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((343093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -203641/1000000) (δ := 7261/1000000000) (ψ := -818081/1000000) 144 117
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t163 : ((3358893021/62500000000 : ℚ) : ℝ) ≤ stT144 163 := by
  have hc : ((85767/125000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3358893021/62500000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((85767/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c164 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((249453/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 82711/5000000) (δ := 7261/1000000000) (ψ := -818081/1000000) 144 117
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t164 : ((97390052177/1250000000000 : ℚ) : ℝ) ≤ stT144 164 := by
  have hc : ((498881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97390052177/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((498881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c165 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((29427/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1176931/5000000) (δ := 7261/1000000000) (ψ := -818081/1000000) 144 117
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t165 : ((22906914401/500000000000 : ℚ) : ℝ) ≤ stT144 165 := by
  have hc : ((58849/100000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22906914401/500000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((58849/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c166 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-119259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 452909/1000000) (δ := 7261/1000000000) (ψ := -818081/1000000) 144 117
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t166 : ((-23145598971/1250000000000 : ℚ) : ℝ) ≤ stT144 166 := by
  have hc : ((-29821/125000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23145598971/1250000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-29821/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c167 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-446893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3345643/5000000) (δ := 7261/1000000000) (ψ := -818081/1000000) 144 117
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t167 : ((-2701842769/39062500000 : ℚ) : ℝ) ≤ stT144 167 := by
  have hc : ((-223459/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2701842769/39062500000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-223459/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c168 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-115393/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6867441/10000000) (δ := 7249/1000000000) (ψ := -818081/1000000) 144 118
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t168 : ((-356129932649/5000000000000 : ℚ) : ℝ) ≤ stT144 168 := by
  have hc : ((-461597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-356129932649/5000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-461597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c169 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-63211/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4730913/10000000) (δ := 7249/1000000000) (ψ := -818081/1000000) 144 118
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t169 : ((-48631553051/2000000000000 : ℚ) : ℝ) ≤ stT144 169 := by
  have hc : ((-63221/200000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48631553051/2000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-63221/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c170 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((125949/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2607021/10000000) (δ := 7249/1000000000) (ψ := -818081/1000000) 144 118
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t170 : ((48294380893/1250000000000 : ℚ) : ℝ) ≤ stT144 170 := by
  have hc : ((251873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48294380893/1250000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((251873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c171 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((15319/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -99117/2000000) (δ := 7249/1000000000) (ψ := -818081/1000000) 144 118
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t171 : ((374852253577/5000000000000 : ℚ) : ℝ) ≤ stT144 171 := by
  have hc : ((490183/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((374852253577/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((490183/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c172 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((641/800 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1603539/10000000) (δ := 7249/1000000000) (ψ := -818081/1000000) 144 118
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t172 : ((381817869/6250000000 : ℚ) : ℝ) ≤ stT144 172 := by
  have hc : ((2003/2500 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((381817869/6250000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((2003/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c173 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((94457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 738099/2000000) (δ := 7249/1000000000) (ψ := -818081/1000000) 144 118
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t173 : ((14355245199/2000000000000 : ℚ) : ℝ) ≤ stT144 173 := by
  have hc : ((94407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14355245199/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((94407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c174 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-134173/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5765427/10000000) (δ := 7249/1000000000) (ψ := -818081/1000000) 144 118
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t174 : ((-101723998117/2000000000000 : ℚ) : ℝ) ≤ stT144 174 := by
  have hc : ((-134183/200000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101723998117/2000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-134183/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c175 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-249987/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7828479/10000000) (δ := 7249/1000000000) (ψ := -818081/1000000) 144 118
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t175 : ((-377963744071/5000000000000 : ℚ) : ℝ) ≤ stT144 175 := by
  have hc : ((-499999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-377963744071/5000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-499999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c176 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-689273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1457051/2500000) (δ := 1839/250000000) (ψ := -818081/1000000) 144 119
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t176 : ((-519597201617/10000000000000 : ℚ) : ℝ) ≤ stT144 176 := by
  have hc : ((-689323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-519597201617/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-689323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c177 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((27681/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -947129/2500000) (δ := 1839/250000000) (ψ := -818081/1000000) 144 119
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t177 : ((1299220111/312500000000 : ℚ) : ℝ) ≤ stT144 177 := by
  have hc : ((3457/62500 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1299220111/312500000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((3457/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c178 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((762169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -440087/2500000) (δ := 1839/250000000) (ψ := -818081/1000000) 144 119
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t178 : ((571231816189/10000000000000 : ℚ) : ℝ) ≤ stT144 178 := by
  have hc : ((762119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((571231816189/10000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((762119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c179 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((497371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1603/62500) (δ := 1839/250000000) (ψ := -818081/1000000) 144 119
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t179 : ((37173380751/500000000000 : ℚ) : ℝ) ≤ stT144 179 := by
  have hc : ((248673/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37173380751/500000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((248673/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c180 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((61783/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56551/250000) (δ := 1839/250000000) (ψ := -818081/1000000) 144 119
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t180 : ((4604654119/100000000000 : ℚ) : ℝ) ≤ stT144 180 := by
  have hc : ((30889/50000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4604654119/100000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((30889/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c181 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-131427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33254/78125) (δ := 1839/250000000) (ψ := -818081/1000000) 144 119
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t181 : ((-19545239343/2000000000000 : ℚ) : ℝ) ≤ stT144 181 := by
  have hc : ((-131477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19545239343/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-131477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c182 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-49921/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 194999/312500) (δ := 1839/250000000) (ψ := -818081/1000000) 144 119
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t182 : ((-236840049/4000000000 : ℚ) : ℝ) ≤ stT144 182 := by
  have hc : ((-399393/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236840049/4000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-399393/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c183 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-98973/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -468461/625000) (δ := 367/50000000) (ψ := -818081/1000000) 144 120
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t183 : ((-18291678779/250000000000 : ℚ) : ℝ) ≤ stT144 183 := by
  have hc : ((-49489/50000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18291678779/250000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-49489/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c184 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-74911/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -69169/125000) (δ := 367/50000000) (ψ := -818081/1000000) 144 120
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t184 : ((-22091898349/500000000000 : ℚ) : ℝ) ≤ stT144 184 := by
  have hc : ((-299669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22091898349/500000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-299669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c185 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((68723/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -895571/2500000) (δ := 367/50000000) (ψ := -818081/1000000) 144 120
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t185 : ((12626932843/1250000000000 : ℚ) : ℝ) ≤ stT144 185 := by
  have hc : ((34349/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12626932843/1250000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((34349/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c186 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((792049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -410399/2500000) (δ := 367/50000000) (ψ := -818081/1000000) 144 120
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t186 : ((116144277353/2000000000000 : ℚ) : ℝ) ≤ stT144 186 := by
  have hc : ((791999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116144277353/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((791999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c187 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((496669/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72181/2500000) (δ := 367/50000000) (ψ := -818081/1000000) 144 120
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t187 : ((11349432849/156250000000 : ℚ) : ℝ) ≤ stT144 187 := by
  have hc : ((124161/125000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11349432849/156250000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((124161/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c188 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((634461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 276089/1250000) (δ := 367/50000000) (ψ := -818081/1000000) 144 120
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t188 : ((115672792041/2500000000000 : ℚ) : ℝ) ≤ stT144 188 := by
  have hc : ((634411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115672792041/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((634411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c189 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-19137/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1029637/2500000) (δ := 367/50000000) (ψ := -818081/1000000) 144 120
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t189 : ((-27858424507/5000000000000 : ℚ) : ℝ) ≤ stT144 189 := by
  have hc : ((-38299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27858424507/5000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-38299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c190 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-74231/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1504567/2500000) (δ := 367/50000000) (ψ := -818081/1000000) 144 120
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t190 : ((-13464127643/250000000000 : ℚ) : ℝ) ≤ stT144 190 := by
  have hc : ((-18559/25000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13464127643/250000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-18559/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c191 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-499883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7799911/10000000) (δ := 7233/1000000000) (ψ := -818081/1000000) 144 121
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t191 : ((-3617209311/50000000000 : ℚ) : ℝ) ≤ stT144 191 := by
  have hc : ((-124977/125000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3617209311/50000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-124977/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c192 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-715413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5920027/10000000) (δ := 7233/1000000000) (ψ := -818081/1000000) 144 121
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t192 : ((-64542632693/1250000000000 : ℚ) : ℝ) ≤ stT144 192 := by
  have hc : ((-715463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64542632693/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-715463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c193 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-49143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4049899/10000000) (δ := 7233/1000000000) (ψ := -818081/1000000) 144 121
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t193 : ((-4426238561/1250000000000 : ℚ) : ℝ) ≤ stT144 193 := by
  have hc : ((-49193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4426238561/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-49193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c194 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((80051/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2189419/10000000) (δ := 7233/1000000000) (ψ := -818081/1000000) 144 121
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t194 : ((114937537241/2500000000000 : ℚ) : ℝ) ≤ stT144 194 := by
  have hc : ((320179/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114937537241/2500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((320179/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c195 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((990847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -67703/2000000) (δ := 7233/1000000000) (ψ := -818081/1000000) 144 121
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t195 : ((354761801429/5000000000000 : ℚ) : ℝ) ≤ stT144 195 := by
  have hc : ((990797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((354761801429/5000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((990797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c196 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((32987/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1502921/10000000) (δ := 7233/1000000000) (ψ := -818081/1000000) 144 121
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t196 : ((942427629/16000000000 : ℚ) : ℝ) ≤ stT144 196 := by
  have hc : ((6597/8000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((942427629/16000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((6597/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c197 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((234591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3334997/10000000) (δ := 7233/1000000000) (ψ := -818081/1000000) 144 121
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t197 : ((16710342627/1000000000000 : ℚ) : ℝ) ≤ stT144 197 := by
  have hc : ((234541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16710342627/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((234541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c198 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-47267/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1031557/2000000) (δ := 7233/1000000000) (ψ := -818081/1000000) 144 121
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t198 : ((-419934903/12500000000 : ℚ) : ℝ) ≤ stT144 198 := by
  have hc : ((-5909/12500 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-419934903/12500000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-5909/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c199 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-117291/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6971393/10000000) (δ := 7233/1000000000) (ψ := -818081/1000000) 144 121
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t199 : ((-166299818349/2500000000000 : ℚ) : ℝ) ≤ stT144 199 := by
  have hc : ((-469189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166299818349/2500000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-469189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c200 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-932773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -693207/1000000) (δ := 7277/1000000000) (ψ := -818081/1000000) 144 122
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t200 : ((-659605673061/10000000000000 : ℚ) : ℝ) ≤ stT144 200 := by
  have hc : ((-932823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-659605673061/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-932823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c201 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-232581/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2568267/5000000) (δ := 7277/1000000000) (ψ := -818081/1000000) 144 122
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t201 : ((-41016927919/1250000000000 : ℚ) : ℝ) ≤ stT144 201 := by
  have hc : ((-116303/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41016927919/1250000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-116303/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c202 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((7149/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1674981/5000000) (δ := 7277/1000000000) (ψ := -818081/1000000) 144 122
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t202 : ((80462649323/5000000000000 : ℚ) : ℝ) ≤ stT144 202 := by
  have hc : ((114359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80462649323/5000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((114359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c203 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((808693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -786087/5000000) (δ := 7277/1000000000) (ψ := -818081/1000000) 144 122
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t203 : ((283777896633/5000000000000 : ℚ) : ℝ) ≤ stT144 203 := by
  have hc : ((808643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((283777896633/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((808643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c204 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((996901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 98433/5000000) (δ := 7277/1000000000) (ψ := -818081/1000000) 144 122
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t204 : ((34896762957/500000000000 : ℚ) : ℝ) ≤ stT144 204 := by
  have hc : ((996851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34896762957/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((996851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c205 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((708867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 978633/5000000) (δ := 7277/1000000000) (ψ := -818081/1000000) 144 122
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t205 : ((49505905731/1000000000000 : ℚ) : ℝ) ≤ stT144 205 := by
  have hc : ((708817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49505905731/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((708817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c206 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((87047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1854549/5000000) (δ := 7277/1000000000) (ψ := -818081/1000000) 144 122
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t206 : ((60613680801/10000000000000 : ℚ) : ℝ) ≤ stT144 206 := by
  have hc : ((86997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60613680801/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((86997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c207 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-573013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2726217/5000000) (δ := 7277/1000000000) (ψ := -818081/1000000) 144 122
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t207 : ((-398306865087/10000000000000 : ℚ) : ℝ) ≤ stT144 207 := by
  have hc : ((-573063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-398306865087/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-573063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c208 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-482331/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3593691/5000000) (δ := 7277/1000000000) (ψ := -818081/1000000) 144 122
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t208 : ((-653230613/9765625000 : ℚ) : ℝ) ≤ stT144 208 := by
  have hc : ((-120589/125000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-653230613/9765625000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-120589/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c209 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-182289/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6793949/10000000) (δ := 1477/200000000) (ψ := -818081/1000000) 144 123
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t209 : ((-25219790557/400000000000 : ℚ) : ℝ) ≤ stT144 209 := by
  have hc : ((-182299/200000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25219790557/400000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-182299/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c210 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-110859/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5075561/10000000) (δ := 1477/200000000) (ψ := -818081/1000000) 144 123
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t210 : ((-76508652519/2500000000000 : ℚ) : ℝ) ≤ stT144 210 := by
  have hc : ((-221743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76508652519/2500000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-221743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c211 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((222773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -673069/2000000) (δ := 1477/200000000) (ψ := -818081/1000000) 144 123
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t211 : ((38332187361/2500000000000 : ℚ) : ℝ) ≤ stT144 211 := by
  have hc : ((222723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38332187361/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((222723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c212 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((786737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1663229/10000000) (δ := 1477/200000000) (ψ := -818081/1000000) 144 123
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t212 : ((270149102487/5000000000000 : ℚ) : ℝ) ≤ stT144 212 := by
  have hc : ((786687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270149102487/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((786687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c213 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((249981/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6179/2000000) (δ := 1477/200000000) (ψ := -818081/1000000) 144 123
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t213 : ((85637708289/1250000000000 : ℚ) : ℝ) ≤ stT144 213 := by
  have hc : ((499937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85637708289/1250000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((499937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c214 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((386627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1717099/10000000) (δ := 1477/200000000) (ψ := -818081/1000000) 144 123
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t214 : ((26427532817/500000000000 : ℚ) : ℝ) ≤ stT144 214 := by
  have hc : ((193301/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26427532817/500000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((193301/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c215 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((21103/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3395419/10000000) (δ := 1477/200000000) (ψ := -818081/1000000) 144 123
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t215 : ((3597177353/250000000000 : ℚ) : ℝ) ≤ stT144 215 := by
  have hc : ((10549/50000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3597177353/250000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((10549/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c216 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-439991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5065963/10000000) (δ := 1477/200000000) (ψ := -818081/1000000) 144 123
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t216 : ((-149705028487/5000000000000 : ℚ) : ℝ) ≤ stT144 216 := by
  have hc : ((-440041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149705028487/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-440041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c217 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-90041/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6728767/10000000) (δ := 1477/200000000) (ψ := -818081/1000000) 144 123
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t217 : ((-6112727687/100000000000 : ℚ) : ℝ) ≤ stT144 217 := by
  have hc : ((-45023/50000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6112727687/100000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-45023/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c218 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-61101/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -292961/400000) (δ := 7311/1000000000) (ψ := -818081/1000000) 144 124
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t218 : ((-165539873619/2500000000000 : ℚ) : ℝ) ≤ stT144 218 := by
  have hc : ((-488833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165539873619/2500000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-488833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c219 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-644041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5676413/10000000) (δ := 7311/1000000000) (ψ := -818081/1000000) 144 124
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t219 : ((-217618382079/5000000000000 : ℚ) : ℝ) ≤ stT144 219 := by
  have hc : ((-644091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217618382079/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-644091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c220 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-1093/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -161453/400000) (δ := 7311/1000000000) (ψ := -818081/1000000) 144 124
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t220 : ((-14754867/5000000000 : ℚ) : ℝ) ≤ stT144 220 := by
  have hc : ((-4377/100000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14754867/5000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-4377/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c221 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((286161/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2403653/10000000) (δ := 7311/1000000000) (ψ := -818081/1000000) 144 124
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t221 : ((751858107/19531250000 : ℚ) : ℝ) ≤ stT144 221 := by
  have hc : ((35767/62500 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((751858107/19531250000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((35767/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c222 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((475959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -778397/10000000) (δ := 7311/1000000000) (ψ := -818081/1000000) 144 124
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t222 : ((39928244963/625000000000 : ℚ) : ℝ) ≤ stT144 222 := by
  have hc : ((237967/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39928244963/625000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((237967/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c223 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((118017/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 839587/10000000) (δ := 7311/1000000000) (ψ := -818081/1000000) 144 124
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t223 : ((316103122907/5000000000000 : ℚ) : ℝ) ≤ stT144 223 := by
  have hc : ((472043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((316103122907/5000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((472043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c224 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((556911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 490067/2000000) (δ := 7311/1000000000) (ψ := -818081/1000000) 144 124
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t224 : ((372068347733/10000000000000 : ℚ) : ℝ) ≤ stT144 224 := by
  have hc : ((556861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((372068347733/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((556861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c225 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-50749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4053919/10000000) (δ := 7311/1000000000) (ψ := -818081/1000000) 144 124
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t225 : ((-33866016933/10000000000000 : ℚ) : ℝ) ≤ stT144 225 := by
  have hc : ((-50799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33866016933/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-50799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c226 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-636033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5650357/10000000) (δ := 14511/1000000000) (ψ := -818081/1000000) 144 124
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t226 : ((-423116686853/10000000000000 : ℚ) : ℝ) ≤ stT144 226 := by
  have hc : ((-636083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-423116686853/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-636083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c227 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-242493/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 289591/400000) (δ := 7311/1000000000) (ψ := -818081/1000000) 144 124
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t227 : ((-80478360241/1250000000000 : ℚ) : ℝ) ≤ stT144 227 := by
  have hc : ((-485011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80478360241/1250000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-485011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c228 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-462969/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1721443/2500000) (δ := 1801/250000000) (ψ := -818081/1000000) 144 125
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t228 : ((-153312823699/2500000000000 : ℚ) : ℝ) ≤ stT144 228 := by
  have hc : ((-231497/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153312823699/2500000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-231497/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c229 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-525507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1327567/2500000) (δ := 1801/250000000) (ψ := -818081/1000000) 144 125
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t229 : ((-347298051183/10000000000000 : ℚ) : ℝ) ≤ stT144 229 := by
  have hc : ((-525557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-347298051183/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-525557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c230 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((9259/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -93541/250000) (δ := 1801/250000000) (ψ := -818081/1000000) 144 125
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t230 : ((1220215659/250000000000 : ℚ) : ℝ) ≤ stT144 230 := by
  have hc : ((37011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1220215659/250000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((37011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c231 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((643353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -272477/1250000) (δ := 1801/250000000) (ψ := -818081/1000000) 144 125
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t231 : ((423261852153/10000000000000 : ℚ) : ℝ) ≤ stT144 231 := by
  have hc : ((643303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((423261852153/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((643303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c232 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((121117/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15619/250000) (δ := 1801/250000000) (ψ := -818081/1000000) 144 125
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t232 : ((79513082919/1250000000000 : ℚ) : ℝ) ≤ stT144 232 := by
  have hc : ((484443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79513082919/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((484443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c233 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((37301/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 230909/2500000) (δ := 1801/250000000) (ψ := -818081/1000000) 144 125
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t233 : ((24435358179/400000000000 : ℚ) : ℝ) ≤ stT144 233 := by
  have hc : ((37299/40000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24435358179/400000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((37299/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c234 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((551893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19261/78125) (δ := 1801/250000000) (ψ := -818081/1000000) 144 125
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t234 : ((9018770149/250000000000 : ℚ) : ℝ) ≤ stT144 234 := by
  have hc : ((551843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9018770149/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((551843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c235 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-7359/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 250037/625000) (δ := 1801/250000000) (ψ := -818081/1000000) 144 125
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t235 : ((-9617286447/5000000000000 : ℚ) : ℝ) ≤ stT144 235 := by
  have hc : ((-14743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9617286447/5000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-14743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c236 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-597923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 276463/500000) (δ := 1801/250000000) (ψ := -818081/1000000) 144 125
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t236 : ((-77849506897/2000000000000 : ℚ) : ℝ) ≤ stT144 236 := by
  have hc : ((-597973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77849506897/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-597973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c237 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-237229/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 881431/1250000) (δ := 1801/250000000) (ψ := -818081/1000000) 144 125
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t237 : ((-30820992231/500000000000 : ℚ) : ℝ) ≤ stT144 237 := by
  have hc : ((-474483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30820992231/500000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-474483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c238 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-479789/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1428147/2000000) (δ := 3653/500000000) (ψ := -818081/1000000) 144 126
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t238 : ((-38877169257/625000000000 : ℚ) : ℝ) ≤ stT144 238 := by
  have hc : ((-239907/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38877169257/625000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-239907/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c239 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-63013/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5631291/10000000) (δ := 3653/500000000) (ψ := -818081/1000000) 144 126
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t239 : ((-20381502123/500000000000 : ℚ) : ℝ) ≤ stT144 239 := by
  have hc : ((-31509/50000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20381502123/500000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-31509/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c240 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-10047/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4128147/10000000) (δ := 3653/500000000) (ψ := -818081/1000000) 144 126
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t240 : ((-12978705537/2500000000000 : ℚ) : ℝ) ≤ stT144 240 := by
  have hc : ((-40213/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12978705537/2500000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-40213/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c241 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((99079/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2631267/10000000) (δ := 3653/500000000) (ψ := -818081/1000000) 144 126
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t241 : ((15953972691/500000000000 : ℚ) : ℝ) ≤ stT144 241 := by
  have hc : ((99069/200000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15953972691/500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((99069/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c242 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((897719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1140579/10000000) (δ := 3653/500000000) (ψ := -818081/1000000) 144 126
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t242 : ((72130397157/1250000000000 : ℚ) : ℝ) ≤ stT144 242 := by
  have hc : ((897669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72130397157/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((897669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c243 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((990551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 343953/10000000) (δ := 3653/500000000) (ψ := -818081/1000000) 144 126
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t243 : ((1270812783/20000000000 : ℚ) : ℝ) ≤ stT144 243 := by
  have hc : ((990501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1270812783/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((990501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c244 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((745867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1822401/10000000) (δ := 3653/500000000) (ψ := -818081/1000000) 144 126
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t244 : ((59682513791/1250000000000 : ℚ) : ℝ) ≤ stT144 244 := by
  have hc : ((745817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59682513791/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((745817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c245 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((62549/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3294783/10000000) (δ := 7253/500000000) (ψ := -818081/1000000) 144 126
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t245 : ((19976534487/1250000000000 : ℚ) : ℝ) ≤ stT144 245 := by
  have hc : ((125073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19976534487/1250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((125073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c246 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-163761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4761189/10000000) (δ := 3653/500000000) (ψ := -818081/1000000) 144 126
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t246 : ((-52213093261/2500000000000 : ℚ) : ℝ) ≤ stT144 246 := by
  have hc : ((-81893/250000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52213093261/2500000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-81893/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c247 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-397151/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6221637/10000000) (δ := 3653/500000000) (ψ := -818081/1000000) 144 126
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t247 : ((-6317928279/125000000000 : ℚ) : ℝ) ≤ stT144 247 := by
  have hc : ((-49647/62500 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6317928279/125000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-49647/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c248 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-31171/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7676181/10000000) (δ := 3653/500000000) (ψ := -818081/1000000) 144 126
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t248 : ((-316713733761/5000000000000 : ℚ) : ℝ) ≤ stT144 248 := by
  have hc : ((-498761/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-316713733761/5000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-498761/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c249 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-873549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6583107/10000000) (δ := 739/100000000) (ψ := -818081/1000000) 144 127
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t249 : ((-22144861051/400000000000 : ℚ) : ℝ) ≤ stT144 249 := by
  have hc : ((-873599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22144861051/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-873599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_c250 :
    |Real.cos (((144 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-58307/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5140191/10000000) (δ := 739/100000000) (ψ := -818081/1000000) 144 127
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st144_t250 : ((-18440282421/625000000000 : ℚ) : ℝ) ≤ stT144 250 := by
  have hc : ((-233253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((144 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st144_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18440282421/625000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-233253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st144_p1 : ((683573/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT144 (i+1) := by
  rw [Finset.sum_range_one]
  exact st144_t1

theorem st144_p2 : ((3467726065977/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT144 (i+1))
      = (∑ i ∈ Finset.range 1, stT144 (i+1)) + stT144 2 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 1
    simpa using h
  have hprev := st144_p1
  have hstep := st144_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p3 : ((737161932939/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT144 (i+1))
      = (∑ i ∈ Finset.range 2, stT144 (i+1)) + stT144 3 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 2
    simpa using h
  have hprev := st144_p2
  have hstep := st144_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p4 : ((991943182939/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT144 (i+1))
      = (∑ i ∈ Finset.range 3, stT144 (i+1)) + stT144 4 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 3
    simpa using h
  have hprev := st144_p3
  have hstep := st144_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p5 : ((20320977055399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT144 (i+1))
      = (∑ i ∈ Finset.range 4, stT144 (i+1)) + stT144 5 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 4
    simpa using h
  have hprev := st144_p4
  have hstep := st144_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p6 : ((4344092826489/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT144 (i+1))
      = (∑ i ∈ Finset.range 5, stT144 (i+1)) + stT144 6 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 5
    simpa using h
  have hprev := st144_p5
  have hstep := st144_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p7 : ((2118012986289/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT144 (i+1))
      = (∑ i ∈ Finset.range 6, stT144 (i+1)) + stT144 7 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 6
    simpa using h
  have hprev := st144_p6
  have hstep := st144_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p8 : ((22005121739709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT144 (i+1))
      = (∑ i ∈ Finset.range 7, stT144 (i+1)) + stT144 8 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 7
    simpa using h
  have hprev := st144_p7
  have hstep := st144_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p9 : ((18682941075273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT144 (i+1))
      = (∑ i ∈ Finset.range 8, stT144 (i+1)) + stT144 9 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 8
    simpa using h
  have hprev := st144_p8
  have hstep := st144_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p10 : ((5314814408501/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT144 (i+1))
      = (∑ i ∈ Finset.range 9, stT144 (i+1)) + stT144 10 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 9
    simpa using h
  have hprev := st144_p9
  have hstep := st144_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p11 : ((23845497945771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT144 (i+1))
      = (∑ i ∈ Finset.range 10, stT144 (i+1)) + stT144 11 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 10
    simpa using h
  have hprev := st144_p10
  have hstep := st144_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p12 : ((1054977908253/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT144 (i+1))
      = (∑ i ∈ Finset.range 11, stT144 (i+1)) + stT144 12 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 11
    simpa using h
  have hprev := st144_p11
  have hstep := st144_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p13 : ((1150289013873/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT144 (i+1))
      = (∑ i ∈ Finset.range 12, stT144 (i+1)) + stT144 13 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 12
    simpa using h
  have hprev := st144_p12
  have hstep := st144_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p14 : ((26729636803923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT144 (i+1))
      = (∑ i ∈ Finset.range 13, stT144 (i+1)) + stT144 14 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 13
    simpa using h
  have hprev := st144_p13
  have hstep := st144_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p15 : ((27617213252839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT144 (i+1))
      = (∑ i ∈ Finset.range 14, stT144 (i+1)) + stT144 15 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 14
    simpa using h
  have hprev := st144_p14
  have hstep := st144_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p16 : ((26457757789057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT144 (i+1))
      = (∑ i ∈ Finset.range 15, stT144 (i+1)) + stT144 16 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 15
    simpa using h
  have hprev := st144_p15
  have hstep := st144_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p17 : ((28697389728001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT144 (i+1))
      = (∑ i ∈ Finset.range 16, stT144 (i+1)) + stT144 17 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 16
    simpa using h
  have hprev := st144_p16
  have hstep := st144_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p18 : ((27055473364063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT144 (i+1))
      = (∑ i ∈ Finset.range 17, stT144 (i+1)) + stT144 18 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 17
    simpa using h
  have hprev := st144_p17
  have hstep := st144_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p19 : ((25304067263703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT144 (i+1))
      = (∑ i ∈ Finset.range 18, stT144 (i+1)) + stT144 19 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 18
    simpa using h
  have hprev := st144_p18
  have hstep := st144_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p20 : ((516471946131/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT144 (i+1))
      = (∑ i ∈ Finset.range 19, stT144 (i+1)) + stT144 20 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 19
    simpa using h
  have hprev := st144_p19
  have hstep := st144_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p21 : ((552645910837/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT144 (i+1))
      = (∑ i ∈ Finset.range 20, stT144 (i+1)) + stT144 21 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 20
    simpa using h
  have hprev := st144_p20
  have hstep := st144_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p22 : ((14865261511471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT144 (i+1))
      = (∑ i ∈ Finset.range 21, stT144 (i+1)) + stT144 22 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 21
    simpa using h
  have hprev := st144_p21
  have hstep := st144_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p23 : ((15905899540411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT144 (i+1))
      = (∑ i ∈ Finset.range 22, stT144 (i+1)) + stT144 23 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 22
    simpa using h
  have hprev := st144_p22
  have hstep := st144_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p24 : ((16903037603947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT144 (i+1))
      = (∑ i ∈ Finset.range 23, stT144 (i+1)) + stT144 24 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 23
    simpa using h
  have hprev := st144_p23
  have hstep := st144_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p25 : ((17717151603947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT144 (i+1))
      = (∑ i ∈ Finset.range 24, stT144 (i+1)) + stT144 25 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 24
    simpa using h
  have hprev := st144_p24
  have hstep := st144_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p26 : ((36043449620299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT144 (i+1))
      = (∑ i ∈ Finset.range 25, stT144 (i+1)) + stT144 26 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 25
    simpa using h
  have hprev := st144_p25
  have hstep := st144_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p27 : ((4383246799111/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT144 (i+1))
      = (∑ i ∈ Finset.range 26, stT144 (i+1)) + stT144 27 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 26
    simpa using h
  have hprev := st144_p26
  have hstep := st144_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p28 : ((33176119265897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT144 (i+1))
      = (∑ i ∈ Finset.range 27, stT144 (i+1)) + stT144 28 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 27
    simpa using h
  have hprev := st144_p27
  have hstep := st144_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p29 : ((32569695655071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT144 (i+1))
      = (∑ i ∈ Finset.range 28, stT144 (i+1)) + stT144 29 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 28
    simpa using h
  have hprev := st144_p28
  have hstep := st144_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p30 : ((34170048928621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT144 (i+1))
      = (∑ i ∈ Finset.range 29, stT144 (i+1)) + stT144 30 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 29
    simpa using h
  have hprev := st144_p29
  have hstep := st144_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p31 : ((35048947464171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT144 (i+1))
      = (∑ i ∈ Finset.range 30, stT144 (i+1)) + stT144 31 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 30
    simpa using h
  have hprev := st144_p30
  have hstep := st144_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p32 : ((6680250146869/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT144 (i+1))
      = (∑ i ∈ Finset.range 31, stT144 (i+1)) + stT144 32 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 31
    simpa using h
  have hprev := st144_p31
  have hstep := st144_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p33 : ((33245489489939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT144 (i+1))
      = (∑ i ∈ Finset.range 32, stT144 (i+1)) + stT144 33 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 32
    simpa using h
  have hprev := st144_p32
  have hstep := st144_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p34 : ((4358894115773/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT144 (i+1))
      = (∑ i ∈ Finset.range 33, stT144 (i+1)) + stT144 34 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 33
    simpa using h
  have hprev := st144_p33
  have hstep := st144_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p35 : ((33587659044759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT144 (i+1))
      = (∑ i ∈ Finset.range 34, stT144 (i+1)) + stT144 35 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 34
    simpa using h
  have hprev := st144_p34
  have hstep := st144_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p36 : ((33499585693811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT144 (i+1))
      = (∑ i ∈ Finset.range 35, stT144 (i+1)) + stT144 36 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 35
    simpa using h
  have hprev := st144_p35
  have hstep := st144_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p37 : ((17370910796979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT144 (i+1))
      = (∑ i ∈ Finset.range 36, stT144 (i+1)) + stT144 37 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 36
    simpa using h
  have hprev := st144_p36
  have hstep := st144_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p38 : ((2069982509313/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT144 (i+1))
      = (∑ i ∈ Finset.range 37, stT144 (i+1)) + stT144 38 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 37
    simpa using h
  have hprev := st144_p37
  have hstep := st144_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p39 : ((34456067606277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT144 (i+1))
      = (∑ i ∈ Finset.range 38, stT144 (i+1)) + stT144 39 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 38
    simpa using h
  have hprev := st144_p38
  have hstep := st144_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p40 : ((33721321799811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT144 (i+1))
      = (∑ i ∈ Finset.range 39, stT144 (i+1)) + stT144 40 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 39
    simpa using h
  have hprev := st144_p39
  have hstep := st144_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p41 : ((33829059788493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT144 (i+1))
      = (∑ i ∈ Finset.range 40, stT144 (i+1)) + stT144 41 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 40
    simpa using h
  have hprev := st144_p40
  have hstep := st144_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p42 : ((34224727396419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT144 (i+1))
      = (∑ i ∈ Finset.range 41, stT144 (i+1)) + stT144 42 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 41
    simpa using h
  have hprev := st144_p41
  have hstep := st144_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p43 : ((33485290659753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT144 (i+1))
      = (∑ i ∈ Finset.range 42, stT144 (i+1)) + stT144 43 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 42
    simpa using h
  have hprev := st144_p42
  have hstep := st144_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p44 : ((34427359389041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT144 (i+1))
      = (∑ i ∈ Finset.range 43, stT144 (i+1)) + stT144 44 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 43
    simpa using h
  have hprev := st144_p43
  have hstep := st144_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p45 : ((33390023592449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT144 (i+1))
      = (∑ i ∈ Finset.range 44, stT144 (i+1)) + stT144 45 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 44
    simpa using h
  have hprev := st144_p44
  have hstep := st144_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p46 : ((3444033923687/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT144 (i+1))
      = (∑ i ∈ Finset.range 45, stT144 (i+1)) + stT144 46 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 45
    simpa using h
  have hprev := st144_p45
  have hstep := st144_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p47 : ((104524610111/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT144 (i+1))
      = (∑ i ∈ Finset.range 46, stT144 (i+1)) + stT144 47 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 46
    simpa using h
  have hprev := st144_p46
  have hstep := st144_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p48 : ((3430785249427/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT144 (i+1))
      = (∑ i ∈ Finset.range 47, stT144 (i+1)) + stT144 48 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 47
    simpa using h
  have hprev := st144_p47
  have hstep := st144_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p49 : ((134664066093/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT144 (i+1))
      = (∑ i ∈ Finset.range 48, stT144 (i+1)) + stT144 49 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 48
    simpa using h
  have hprev := st144_p48
  have hstep := st144_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p50 : ((16996598764613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT144 (i+1))
      = (∑ i ∈ Finset.range 49, stT144 (i+1)) + stT144 50 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 49
    simpa using h
  have hprev := st144_p49
  have hstep := st144_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p51 : ((17036099963273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT144 (i+1))
      = (∑ i ∈ Finset.range 50, stT144 (i+1)) + stT144 51 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 50
    simpa using h
  have hprev := st144_p50
  have hstep := st144_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p52 : ((16764848694171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT144 (i+1))
      = (∑ i ∈ Finset.range 51, stT144 (i+1)) + stT144 52 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 51
    simpa using h
  have hprev := st144_p51
  have hstep := st144_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p53 : ((17257753112371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT144 (i+1))
      = (∑ i ∈ Finset.range 52, stT144 (i+1)) + stT144 53 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 52
    simpa using h
  have hprev := st144_p52
  have hstep := st144_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p54 : ((16611916391023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT144 (i+1))
      = (∑ i ∈ Finset.range 53, stT144 (i+1)) + stT144 54 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 53
    simpa using h
  have hprev := st144_p53
  have hstep := st144_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p55 : ((34550620991273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT144 (i+1))
      = (∑ i ∈ Finset.range 54, stT144 (i+1)) + stT144 55 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 54
    simpa using h
  have hprev := st144_p54
  have hstep := st144_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p56 : ((33551146206307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT144 (i+1))
      = (∑ i ∈ Finset.range 55, stT144 (i+1)) + stT144 56 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 55
    simpa using h
  have hprev := st144_p55
  have hstep := st144_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p57 : ((6776274115471/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT144 (i+1))
      = (∑ i ∈ Finset.range 56, stT144 (i+1)) + stT144 57 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 56
    simpa using h
  have hprev := st144_p56
  have hstep := st144_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p58 : ((34374620442827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT144 (i+1))
      = (∑ i ∈ Finset.range 57, stT144 (i+1)) + stT144 58 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 57
    simpa using h
  have hprev := st144_p57
  have hstep := st144_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p59 : ((33235582561037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT144 (i+1))
      = (∑ i ∈ Finset.range 58, stT144 (i+1)) + stT144 59 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 58
    simpa using h
  have hprev := st144_p58
  have hstep := st144_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p60 : ((6899317870481/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT144 (i+1))
      = (∑ i ∈ Finset.range 59, stT144 (i+1)) + stT144 60 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 59
    simpa using h
  have hprev := st144_p59
  have hstep := st144_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p61 : ((33780245943547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT144 (i+1))
      = (∑ i ∈ Finset.range 60, stT144 (i+1)) + stT144 61 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 60
    simpa using h
  have hprev := st144_p60
  have hstep := st144_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p62 : ((33519934903609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT144 (i+1))
      = (∑ i ∈ Finset.range 61, stT144 (i+1)) + stT144 62 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 61
    simpa using h
  have hprev := st144_p61
  have hstep := st144_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p63 : ((34608887848339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT144 (i+1))
      = (∑ i ∈ Finset.range 62, stT144 (i+1)) + stT144 63 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 62
    simpa using h
  have hprev := st144_p62
  have hstep := st144_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p64 : ((33433309407877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT144 (i+1))
      = (∑ i ∈ Finset.range 63, stT144 (i+1)) + stT144 64 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 63
    simpa using h
  have hprev := st144_p63
  have hstep := st144_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p65 : ((33817353088099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT144 (i+1))
      = (∑ i ∈ Finset.range 64, stT144 (i+1)) + stT144 65 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 64
    simpa using h
  have hprev := st144_p64
  have hstep := st144_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p66 : ((34540707085683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT144 (i+1))
      = (∑ i ∈ Finset.range 65, stT144 (i+1)) + stT144 66 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 65
    simpa using h
  have hprev := st144_p65
  have hstep := st144_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p67 : ((16659819407609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT144 (i+1))
      = (∑ i ∈ Finset.range 66, stT144 (i+1)) + stT144 67 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 66
    simpa using h
  have hprev := st144_p66
  have hstep := st144_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p68 : ((16965799895213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT144 (i+1))
      = (∑ i ∈ Finset.range 67, stT144 (i+1)) + stT144 68 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 67
    simpa using h
  have hprev := st144_p67
  have hstep := st144_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p69 : ((17259800076683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT144 (i+1))
      = (∑ i ∈ Finset.range 68, stT144 (i+1)) + stT144 69 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 68
    simpa using h
  have hprev := st144_p68
  have hstep := st144_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p70 : ((16662180795767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT144 (i+1))
      = (∑ i ∈ Finset.range 69, stT144 (i+1)) + stT144 70 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 69
    simpa using h
  have hprev := st144_p69
  have hstep := st144_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p71 : ((16926975372487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT144 (i+1))
      = (∑ i ∈ Finset.range 70, stT144 (i+1)) + stT144 71 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 70
    simpa using h
  have hprev := st144_p70
  have hstep := st144_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p72 : ((8645264169161/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT144 (i+1))
      = (∑ i ∈ Finset.range 71, stT144 (i+1)) + stT144 72 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 71
    simpa using h
  have hprev := st144_p71
  have hstep := st144_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p73 : ((522606723507/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT144 (i+1))
      = (∑ i ∈ Finset.range 72, stT144 (i+1)) + stT144 73 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 72
    simpa using h
  have hprev := st144_p72
  have hstep := st144_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p74 : ((8401930117569/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT144 (i+1))
      = (∑ i ∈ Finset.range 73, stT144 (i+1)) + stT144 74 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 73
    simpa using h
  have hprev := st144_p73
  have hstep := st144_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p75 : ((4327554675447/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT144 (i+1))
      = (∑ i ∈ Finset.range 74, stT144 (i+1)) + stT144 75 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 74
    simpa using h
  have hprev := st144_p74
  have hstep := st144_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p76 : ((16884050176313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT144 (i+1))
      = (∑ i ∈ Finset.range 75, stT144 (i+1)) + stT144 76 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 75
    simpa using h
  have hprev := st144_p75
  have hstep := st144_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p77 : ((8325405502457/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT144 (i+1))
      = (∑ i ∈ Finset.range 76, stT144 (i+1)) + stT144 77 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 76
    simpa using h
  have hprev := st144_p76
  have hstep := st144_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p78 : ((34423634918823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT144 (i+1))
      = (∑ i ∈ Finset.range 77, stT144 (i+1)) + stT144 78 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 77
    simpa using h
  have hprev := st144_p77
  have hstep := st144_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p79 : ((34278571697543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT144 (i+1))
      = (∑ i ∈ Finset.range 78, stT144 (i+1)) + stT144 79 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 78
    simpa using h
  have hprev := st144_p78
  have hstep := st144_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p80 : ((33236059776209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT144 (i+1))
      = (∑ i ∈ Finset.range 79, stT144 (i+1)) + stT144 80 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 79
    simpa using h
  have hprev := st144_p79
  have hstep := st144_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p81 : ((33852186381263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT144 (i+1))
      = (∑ i ∈ Finset.range 80, stT144 (i+1)) + stT144 81 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 80
    simpa using h
  have hprev := st144_p80
  have hstep := st144_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p82 : ((17317069842649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT144 (i+1))
      = (∑ i ∈ Finset.range 81, stT144 (i+1)) + stT144 82 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 81
    simpa using h
  have hprev := st144_p81
  have hstep := st144_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p83 : ((6747154534861/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT144 (i+1))
      = (∑ i ∈ Finset.range 82, stT144 (i+1)) + stT144 83 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 82
    simpa using h
  have hprev := st144_p82
  have hstep := st144_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p84 : ((6650578231037/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT144 (i+1))
      = (∑ i ∈ Finset.range 83, stT144 (i+1)) + stT144 84 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 83
    simpa using h
  have hprev := st144_p83
  have hstep := st144_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p85 : ((34280694374561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT144 (i+1))
      = (∑ i ∈ Finset.range 84, stT144 (i+1)) + stT144 85 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 84
    simpa using h
  have hprev := st144_p84
  have hstep := st144_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p86 : ((3450712902631/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT144 (i+1))
      = (∑ i ∈ Finset.range 85, stT144 (i+1)) + stT144 86 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 85
    simpa using h
  have hprev := st144_p85
  have hstep := st144_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p87 : ((8360593216429/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT144 (i+1))
      = (∑ i ∈ Finset.range 86, stT144 (i+1)) + stT144 87 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 86
    simpa using h
  have hprev := st144_p86
  have hstep := st144_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p88 : ((8349202963689/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT144 (i+1))
      = (∑ i ∈ Finset.range 87, stT144 (i+1)) + stT144 88 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 87
    simpa using h
  have hprev := st144_p87
  have hstep := st144_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p89 : ((6891331455037/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT144 (i+1))
      = (∑ i ∈ Finset.range 88, stT144 (i+1)) + stT144 89 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 88
    simpa using h
  have hprev := st144_p88
  have hstep := st144_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p90 : ((3440203944639/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT144 (i+1))
      = (∑ i ∈ Finset.range 89, stT144 (i+1)) + stT144 90 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 89
    simpa using h
  have hprev := st144_p89
  have hstep := st144_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p91 : ((6671286143599/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT144 (i+1))
      = (∑ i ∈ Finset.range 90, stT144 (i+1)) + stT144 91 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 90
    simpa using h
  have hprev := st144_p90
  have hstep := st144_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p92 : ((33434661150587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT144 (i+1))
      = (∑ i ∈ Finset.range 91, stT144 (i+1)) + stT144 92 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 91
    simpa using h
  have hprev := st144_p91
  have hstep := st144_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p93 : ((34469623278569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT144 (i+1))
      = (∑ i ∈ Finset.range 92, stT144 (i+1)) + stT144 93 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 92
    simpa using h
  have hprev := st144_p92
  have hstep := st144_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p94 : ((1377526513789/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT144 (i+1))
      = (∑ i ∈ Finset.range 93, stT144 (i+1)) + stT144 94 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 93
    simpa using h
  have hprev := st144_p93
  have hstep := st144_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p95 : ((33412272078919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT144 (i+1))
      = (∑ i ∈ Finset.range 94, stT144 (i+1)) + stT144 95 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 94
    simpa using h
  have hprev := st144_p94
  have hstep := st144_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p96 : ((16665610751723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT144 (i+1))
      = (∑ i ∈ Finset.range 95, stT144 (i+1)) + stT144 96 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 95
    simpa using h
  have hprev := st144_p95
  have hstep := st144_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p97 : ((3433386958637/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT144 (i+1))
      = (∑ i ∈ Finset.range 96, stT144 (i+1)) + stT144 97 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 96
    simpa using h
  have hprev := st144_p96
  have hstep := st144_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p98 : ((17292777509041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT144 (i+1))
      = (∑ i ∈ Finset.range 97, stT144 (i+1)) + stT144 98 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 97
    simpa using h
  have hprev := st144_p97
  have hstep := st144_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p99 : ((16822572490817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT144 (i+1))
      = (∑ i ∈ Finset.range 98, stT144 (i+1)) + stT144 99 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 98
    simpa using h
  have hprev := st144_p98
  have hstep := st144_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p100 : ((16589768990817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT144 (i+1))
      = (∑ i ∈ Finset.range 99, stT144 (i+1)) + stT144 100 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 99
    simpa using h
  have hprev := st144_p99
  have hstep := st144_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p101 : ((33988052310873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT144 (i+1))
      = (∑ i ∈ Finset.range 100, stT144 (i+1)) + stT144 101 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 100
    simpa using h
  have hprev := st144_p100
  have hstep := st144_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p102 : ((17340153327447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT144 (i+1))
      = (∑ i ∈ Finset.range 101, stT144 (i+1)) + stT144 102 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 101
    simpa using h
  have hprev := st144_p101
  have hstep := st144_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p103 : ((17049634688927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT144 (i+1))
      = (∑ i ∈ Finset.range 102, stT144 (i+1)) + stT144 103 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 102
    simpa using h
  have hprev := st144_p102
  have hstep := st144_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p104 : ((519011571787/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT144 (i+1))
      = (∑ i ∈ Finset.range 103, stT144 (i+1)) + stT144 104 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 103
    simpa using h
  have hprev := st144_p103
  have hstep := st144_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p105 : ((4183251353471/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT144 (i+1))
      = (∑ i ∈ Finset.range 104, stT144 (i+1)) + stT144 105 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 104
    simpa using h
  have hprev := st144_p104
  have hstep := st144_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p106 : ((34435909804073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT144 (i+1))
      = (∑ i ∈ Finset.range 105, stT144 (i+1)) + stT144 106 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 105
    simpa using h
  have hprev := st144_p105
  have hstep := st144_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p107 : ((34595783770073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT144 (i+1))
      = (∑ i ∈ Finset.range 106, stT144 (i+1)) + stT144 107 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 106
    simpa using h
  have hprev := st144_p106
  have hstep := st144_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p108 : ((16854243655859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT144 (i+1))
      = (∑ i ∈ Finset.range 107, stT144 (i+1)) + stT144 108 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 107
    simpa using h
  have hprev := st144_p107
  have hstep := st144_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p109 : ((132542505233/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT144 (i+1))
      = (∑ i ∈ Finset.range 108, stT144 (i+1)) + stT144 109 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 108
    simpa using h
  have hprev := st144_p108
  have hstep := st144_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p110 : ((4216334408527/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT144 (i+1))
      = (∑ i ∈ Finset.range 109, stT144 (i+1)) + stT144 110 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 109
    simpa using h
  have hprev := st144_p109
  have hstep := st144_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p111 : ((17301233240573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT144 (i+1))
      = (∑ i ∈ Finset.range 110, stT144 (i+1)) + stT144 111 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 110
    simpa using h
  have hprev := st144_p110
  have hstep := st144_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p112 : ((17241319205389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT144 (i+1))
      = (∑ i ∈ Finset.range 111, stT144 (i+1)) + stT144 112 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 111
    simpa using h
  have hprev := st144_p111
  have hstep := st144_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p113 : ((33554443110893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT144 (i+1))
      = (∑ i ∈ Finset.range 112, stT144 (i+1)) + stT144 113 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 112
    simpa using h
  have hprev := st144_p112
  have hstep := st144_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p114 : ((1325351469921/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT144 (i+1))
      = (∑ i ∈ Finset.range 113, stT144 (i+1)) + stT144 114 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 113
    simpa using h
  have hprev := st144_p113
  have hstep := st144_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p115 : ((6759479711421/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT144 (i+1))
      = (∑ i ∈ Finset.range 114, stT144 (i+1)) + stT144 115 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 114
    simpa using h
  have hprev := st144_p114
  have hstep := st144_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p116 : ((34626048531489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT144 (i+1))
      = (∑ i ∈ Finset.range 115, stT144 (i+1)) + stT144 116 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 115
    simpa using h
  have hprev := st144_p115
  have hstep := st144_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p117 : ((34503282194697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT144 (i+1))
      = (∑ i ∈ Finset.range 116, stT144 (i+1)) + stT144 117 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 116
    simpa using h
  have hprev := st144_p116
  have hstep := st144_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p118 : ((16801647006711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT144 (i+1))
      = (∑ i ∈ Finset.range 117, stT144 (i+1)) + stT144 118 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 117
    simpa using h
  have hprev := st144_p117
  have hstep := st144_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p119 : ((33110321708891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT144 (i+1))
      = (∑ i ∈ Finset.range 118, stT144 (i+1)) + stT144 119 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 118
    simpa using h
  have hprev := st144_p118
  have hstep := st144_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p120 : ((33653462927231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT144 (i+1))
      = (∑ i ∈ Finset.range 119, stT144 (i+1)) + stT144 120 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 119
    simpa using h
  have hprev := st144_p119
  have hstep := st144_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p121 : ((34531592958191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT144 (i+1))
      = (∑ i ∈ Finset.range 120, stT144 (i+1)) + stT144 121 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 120
    simpa using h
  have hprev := st144_p120
  have hstep := st144_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p122 : ((34643585619091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT144 (i+1))
      = (∑ i ∈ Finset.range 121, stT144 (i+1)) + stT144 122 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 121
    simpa using h
  have hprev := st144_p121
  have hstep := st144_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p123 : ((33860762938451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT144 (i+1))
      = (∑ i ∈ Finset.range 122, stT144 (i+1)) + stT144 123 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 122
    simpa using h
  have hprev := st144_p122
  have hstep := st144_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p124 : ((6628799100837/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT144 (i+1))
      = (∑ i ∈ Finset.range 123, stT144 (i+1)) + stT144 124 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 123
    simpa using h
  have hprev := st144_p123
  have hstep := st144_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p125 : ((6670005352727/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT144 (i+1))
      = (∑ i ∈ Finset.range 124, stT144 (i+1)) + stT144 125 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 124
    simpa using h
  have hprev := st144_p124
  have hstep := st144_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p126 : ((6844934091491/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT144 (i+1))
      = (∑ i ∈ Finset.range 125, stT144 (i+1)) + stT144 126 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 125
    simpa using h
  have hprev := st144_p125
  have hstep := st144_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p127 : ((34742627253503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT144 (i+1))
      = (∑ i ∈ Finset.range 126, stT144 (i+1)) + stT144 127 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 126
    simpa using h
  have hprev := st144_p126
  have hstep := st144_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p128 : ((34314124709723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT144 (i+1))
      = (∑ i ∈ Finset.range 127, stT144 (i+1)) + stT144 128 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 127
    simpa using h
  have hprev := st144_p127
  have hstep := st144_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p129 : ((16717502916043/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT144 (i+1))
      = (∑ i ∈ Finset.range 128, stT144 (i+1)) + stT144 129 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 128
    simpa using h
  have hprev := st144_p128
  have hstep := st144_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p130 : ((33091064514059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT144 (i+1))
      = (∑ i ∈ Finset.range 129, stT144 (i+1)) + stT144 130 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 129
    simpa using h
  have hprev := st144_p129
  have hstep := st144_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p131 : ((33654237512083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT144 (i+1))
      = (∑ i ∈ Finset.range 130, stT144 (i+1)) + stT144 131 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 130
    simpa using h
  have hprev := st144_p130
  have hstep := st144_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p132 : ((34502680419439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT144 (i+1))
      = (∑ i ∈ Finset.range 131, stT144 (i+1)) + stT144 132 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 131
    simpa using h
  have hprev := st144_p131
  have hstep := st144_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p133 : ((34724877100689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT144 (i+1))
      = (∑ i ∈ Finset.range 132, stT144 (i+1)) + stT144 133 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 132
    simpa using h
  have hprev := st144_p132
  have hstep := st144_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p134 : ((34093537447157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT144 (i+1))
      = (∑ i ∈ Finset.range 133, stT144 (i+1)) + stT144 134 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 133
    simpa using h
  have hprev := st144_p133
  have hstep := st144_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p135 : ((33276332764679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT144 (i+1))
      = (∑ i ∈ Finset.range 134, stT144 (i+1)) + stT144 135 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 134
    simpa using h
  have hprev := st144_p134
  have hstep := st144_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p136 : ((8278846404011/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT144 (i+1))
      = (∑ i ∈ Finset.range 135, stT144 (i+1)) + stT144 136 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 135
    simpa using h
  have hprev := st144_p135
  have hstep := st144_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p137 : ((33766251011427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT144 (i+1))
      = (∑ i ∈ Finset.range 136, stT144 (i+1)) + stT144 137 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 136
    simpa using h
  have hprev := st144_p136
  have hstep := st144_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p138 : ((34567974127299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT144 (i+1))
      = (∑ i ∈ Finset.range 137, stT144 (i+1)) + stT144 138 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 137
    simpa using h
  have hprev := st144_p137
  have hstep := st144_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p139 : ((34726792241171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT144 (i+1))
      = (∑ i ∈ Finset.range 138, stT144 (i+1)) + stT144 139 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 138
    simpa using h
  have hprev := st144_p138
  have hstep := st144_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p140 : ((34095240025561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT144 (i+1))
      = (∑ i ∈ Finset.range 139, stT144 (i+1)) + stT144 140 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 139
    simpa using h
  have hprev := st144_p139
  have hstep := st144_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p141 : ((33290155345841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT144 (i+1))
      = (∑ i ∈ Finset.range 140, stT144 (i+1)) + stT144 141 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 140
    simpa using h
  have hprev := st144_p140
  have hstep := st144_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p142 : ((6615661944843/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT144 (i+1))
      = (∑ i ∈ Finset.range 141, stT144 (i+1)) + stT144 142 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 141
    simpa using h
  have hprev := st144_p141
  have hstep := st144_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p143 : ((33651567831329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT144 (i+1))
      = (∑ i ∈ Finset.range 142, stT144 (i+1)) + stT144 143 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 142
    simpa using h
  have hprev := st144_p142
  have hstep := st144_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p144 : ((34470165837223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT144 (i+1))
      = (∑ i ∈ Finset.range 143, stT144 (i+1)) + stT144 144 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 143
    simpa using h
  have hprev := st144_p143
  have hstep := st144_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p145 : ((6956583460997/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT144 (i+1))
      = (∑ i ∈ Finset.range 144, stT144 (i+1)) + stT144 145 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 144
    simpa using h
  have hprev := st144_p144
  have hstep := st144_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p146 : ((34313174760233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT144 (i+1))
      = (∑ i ∈ Finset.range 145, stT144 (i+1)) + stT144 146 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 145
    simpa using h
  have hprev := st144_p145
  have hstep := st144_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p147 : ((33488447144897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT144 (i+1))
      = (∑ i ∈ Finset.range 146, stT144 (i+1)) + stT144 147 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 146
    simpa using h
  have hprev := st144_p146
  have hstep := st144_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p148 : ((8259677871633/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT144 (i+1))
      = (∑ i ∈ Finset.range 147, stT144 (i+1)) + stT144 148 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 147
    simpa using h
  have hprev := st144_p147
  have hstep := st144_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p149 : ((33350770501359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT144 (i+1))
      = (∑ i ∈ Finset.range 148, stT144 (i+1)) + stT144 149 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 148
    simpa using h
  have hprev := st144_p148
  have hstep := st144_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p150 : ((6829624097331/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT144 (i+1))
      = (∑ i ∈ Finset.range 149, stT144 (i+1)) + stT144 150 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 149
    simpa using h
  have hprev := st144_p149
  have hstep := st144_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p151 : ((34748998759791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT144 (i+1))
      = (∑ i ∈ Finset.range 150, stT144 (i+1)) + stT144 151 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 150
    simpa using h
  have hprev := st144_p150
  have hstep := st144_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p152 : ((34652040531687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT144 (i+1))
      = (∑ i ∈ Finset.range 151, stT144 (i+1)) + stT144 152 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 151
    simpa using h
  have hprev := st144_p151
  have hstep := st144_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p153 : ((16972575528359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT144 (i+1))
      = (∑ i ∈ Finset.range 152, stT144 (i+1)) + stT144 153 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 152
    simpa using h
  have hprev := st144_p152
  have hstep := st144_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p154 : ((16606551382007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT144 (i+1))
      = (∑ i ∈ Finset.range 153, stT144 (i+1)) + stT144 154 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 153
    simpa using h
  have hprev := st144_p153
  have hstep := st144_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p155 : ((16523834581577/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT144 (i+1))
      = (∑ i ∈ Finset.range 154, stT144 (i+1)) + stT144 155 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 154
    simpa using h
  have hprev := st144_p154
  have hstep := st144_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p156 : ((16787373644297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT144 (i+1))
      = (∑ i ∈ Finset.range 155, stT144 (i+1)) + stT144 156 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 155
    simpa using h
  have hprev := st144_p155
  have hstep := st144_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p157 : ((17185474902817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT144 (i+1))
      = (∑ i ∈ Finset.range 156, stT144 (i+1)) + stT144 157 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 156
    simpa using h
  have hprev := st144_p156
  have hstep := st144_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p158 : ((17406275383711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT144 (i+1))
      = (∑ i ∈ Finset.range 157, stT144 (i+1)) + stT144 158 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 157
    simpa using h
  have hprev := st144_p157
  have hstep := st144_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p159 : ((17281521563169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT144 (i+1))
      = (∑ i ∈ Finset.range 158, stT144 (i+1)) + stT144 159 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 158
    simpa using h
  have hprev := st144_p158
  have hstep := st144_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p160 : ((16909907810109/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT144 (i+1))
      = (∑ i ∈ Finset.range 159, stT144 (i+1)) + stT144 160 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 159
    simpa using h
  have hprev := st144_p159
  have hstep := st144_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p161 : ((2071723195201/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT144 (i+1))
      = (∑ i ∈ Finset.range 160, stT144 (i+1)) + stT144 161 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 160
    simpa using h
  have hprev := st144_p160
  have hstep := st144_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p162 : ((16522868321883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT144 (i+1))
      = (∑ i ∈ Finset.range 161, stT144 (i+1)) + stT144 162 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 161
    simpa using h
  have hprev := st144_p161
  have hstep := st144_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p163 : ((16791579763563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT144 (i+1))
      = (∑ i ∈ Finset.range 162, stT144 (i+1)) + stT144 163 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 162
    simpa using h
  have hprev := st144_p162
  have hstep := st144_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p164 : ((17181139972271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT144 (i+1))
      = (∑ i ∈ Finset.range 163, stT144 (i+1)) + stT144 164 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 163
    simpa using h
  have hprev := st144_p163
  have hstep := st144_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p165 : ((17410209116281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT144 (i+1))
      = (∑ i ∈ Finset.range 164, stT144 (i+1)) + stT144 165 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 164
    simpa using h
  have hprev := st144_p164
  have hstep := st144_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p166 : ((17317626720397/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT144 (i+1))
      = (∑ i ∈ Finset.range 165, stT144 (i+1)) + stT144 166 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 165
    simpa using h
  have hprev := st144_p165
  have hstep := st144_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p167 : ((3394358169193/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT144 (i+1))
      = (∑ i ∈ Finset.range 166, stT144 (i+1)) + stT144 167 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 166
    simpa using h
  have hprev := st144_p166
  have hstep := st144_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p168 : ((4153915228329/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT144 (i+1))
      = (∑ i ∈ Finset.range 167, stT144 (i+1)) + stT144 168 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 167
    simpa using h
  have hprev := st144_p167
  have hstep := st144_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p169 : ((32988164061377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT144 (i+1))
      = (∑ i ∈ Finset.range 168, stT144 (i+1)) + stT144 169 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 168
    simpa using h
  have hprev := st144_p168
  have hstep := st144_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p170 : ((33374519108521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT144 (i+1))
      = (∑ i ∈ Finset.range 169, stT144 (i+1)) + stT144 170 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 169
    simpa using h
  have hprev := st144_p169
  have hstep := st144_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p171 : ((1364968944627/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT144 (i+1))
      = (∑ i ∈ Finset.range 170, stT144 (i+1)) + stT144 171 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 170
    simpa using h
  have hprev := st144_p170
  have hstep := st144_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p172 : ((1389405288243/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT144 (i+1))
      = (∑ i ∈ Finset.range 171, stT144 (i+1)) + stT144 172 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 171
    simpa using h
  have hprev := st144_p171
  have hstep := st144_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p173 : ((3480690843207/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT144 (i+1))
      = (∑ i ∈ Finset.range 172, stT144 (i+1)) + stT144 173 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 172
    simpa using h
  have hprev := st144_p172
  have hstep := st144_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p174 : ((6859657688297/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT144 (i+1))
      = (∑ i ∈ Finset.range 173, stT144 (i+1)) + stT144 174 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 173
    simpa using h
  have hprev := st144_p173
  have hstep := st144_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p175 : ((33542360953343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT144 (i+1))
      = (∑ i ∈ Finset.range 174, stT144 (i+1)) + stT144 175 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 174
    simpa using h
  have hprev := st144_p174
  have hstep := st144_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p176 : ((16511381875863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT144 (i+1))
      = (∑ i ∈ Finset.range 175, stT144 (i+1)) + stT144 176 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 175
    simpa using h
  have hprev := st144_p175
  have hstep := st144_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p177 : ((16532169397639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT144 (i+1))
      = (∑ i ∈ Finset.range 176, stT144 (i+1)) + stT144 177 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 176
    simpa using h
  have hprev := st144_p176
  have hstep := st144_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p178 : ((33635570611467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT144 (i+1))
      = (∑ i ∈ Finset.range 177, stT144 (i+1)) + stT144 178 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 177
    simpa using h
  have hprev := st144_p177
  have hstep := st144_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p179 : ((34379038226487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT144 (i+1))
      = (∑ i ∈ Finset.range 178, stT144 (i+1)) + stT144 179 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 178
    simpa using h
  have hprev := st144_p178
  have hstep := st144_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p180 : ((34839503638387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT144 (i+1))
      = (∑ i ∈ Finset.range 179, stT144 (i+1)) + stT144 180 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 179
    simpa using h
  have hprev := st144_p179
  have hstep := st144_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p181 : ((4342722180209/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT144 (i+1))
      = (∑ i ∈ Finset.range 180, stT144 (i+1)) + stT144 181 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 180
    simpa using h
  have hprev := st144_p180
  have hstep := st144_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p182 : ((8537419329793/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT144 (i+1))
      = (∑ i ∈ Finset.range 181, stT144 (i+1)) + stT144 182 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 181
    simpa using h
  have hprev := st144_p181
  have hstep := st144_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p183 : ((8354502542003/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT144 (i+1))
      = (∑ i ∈ Finset.range 182, stT144 (i+1)) + stT144 183 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 182
    simpa using h
  have hprev := st144_p182
  have hstep := st144_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p184 : ((4122021525129/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT144 (i+1))
      = (∑ i ∈ Finset.range 183, stT144 (i+1)) + stT144 184 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 183
    simpa using h
  have hprev := st144_p183
  have hstep := st144_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p185 : ((1033662114493/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT144 (i+1))
      = (∑ i ∈ Finset.range 184, stT144 (i+1)) + stT144 185 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 184
    simpa using h
  have hprev := st144_p184
  have hstep := st144_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p186 : ((33657909050541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT144 (i+1))
      = (∑ i ∈ Finset.range 185, stT144 (i+1)) + stT144 186 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 185
    simpa using h
  have hprev := st144_p185
  have hstep := st144_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p187 : ((34384272752877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT144 (i+1))
      = (∑ i ∈ Finset.range 186, stT144 (i+1)) + stT144 187 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 186
    simpa using h
  have hprev := st144_p186
  have hstep := st144_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p188 : ((34846963921041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT144 (i+1))
      = (∑ i ∈ Finset.range 187, stT144 (i+1)) + stT144 188 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 187
    simpa using h
  have hprev := st144_p187
  have hstep := st144_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p189 : ((34791247072027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT144 (i+1))
      = (∑ i ∈ Finset.range 188, stT144 (i+1)) + stT144 189 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 188
    simpa using h
  have hprev := st144_p188
  have hstep := st144_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p190 : ((34252681966307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT144 (i+1))
      = (∑ i ∈ Finset.range 189, stT144 (i+1)) + stT144 190 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 189
    simpa using h
  have hprev := st144_p189
  have hstep := st144_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p191 : ((33529240104107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT144 (i+1))
      = (∑ i ∈ Finset.range 190, stT144 (i+1)) + stT144 191 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 190
    simpa using h
  have hprev := st144_p190
  have hstep := st144_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p192 : ((33012899042563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT144 (i+1))
      = (∑ i ∈ Finset.range 191, stT144 (i+1)) + stT144 192 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 191
    simpa using h
  have hprev := st144_p191
  have hstep := st144_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p193 : ((1319099565363/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT144 (i+1))
      = (∑ i ∈ Finset.range 192, stT144 (i+1)) + stT144 193 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 192
    simpa using h
  have hprev := st144_p192
  have hstep := st144_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p194 : ((33437239283039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT144 (i+1))
      = (∑ i ∈ Finset.range 193, stT144 (i+1)) + stT144 194 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 193
    simpa using h
  have hprev := st144_p193
  have hstep := st144_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p195 : ((34146762885897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT144 (i+1))
      = (∑ i ∈ Finset.range 194, stT144 (i+1)) + stT144 195 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 194
    simpa using h
  have hprev := st144_p194
  have hstep := st144_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p196 : ((17367890077011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT144 (i+1))
      = (∑ i ∈ Finset.range 195, stT144 (i+1)) + stT144 196 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 195
    simpa using h
  have hprev := st144_p195
  have hstep := st144_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p197 : ((8725720895073/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT144 (i+1))
      = (∑ i ∈ Finset.range 196, stT144 (i+1)) + stT144 197 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 196
    simpa using h
  have hprev := st144_p196
  have hstep := st144_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p198 : ((8641733914473/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT144 (i+1))
      = (∑ i ∈ Finset.range 197, stT144 (i+1)) + stT144 198 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 197
    simpa using h
  have hprev := st144_p197
  have hstep := st144_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p199 : ((2118858524031/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT144 (i+1))
      = (∑ i ∈ Finset.range 198, stT144 (i+1)) + stT144 199 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 198
    simpa using h
  have hprev := st144_p198
  have hstep := st144_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p200 : ((6648426142287/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT144 (i+1))
      = (∑ i ∈ Finset.range 199, stT144 (i+1)) + stT144 200 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 199
    simpa using h
  have hprev := st144_p199
  have hstep := st144_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p201 : ((32913995288083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT144 (i+1))
      = (∑ i ∈ Finset.range 200, stT144 (i+1)) + stT144 201 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 200
    simpa using h
  have hprev := st144_p200
  have hstep := st144_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p202 : ((33074920586729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT144 (i+1))
      = (∑ i ∈ Finset.range 201, stT144 (i+1)) + stT144 202 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 201
    simpa using h
  have hprev := st144_p201
  have hstep := st144_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p203 : ((6728495275999/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT144 (i+1))
      = (∑ i ∈ Finset.range 202, stT144 (i+1)) + stT144 203 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 202
    simpa using h
  have hprev := st144_p202
  have hstep := st144_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p204 : ((6868082327827/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT144 (i+1))
      = (∑ i ∈ Finset.range 203, stT144 (i+1)) + stT144 204 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 203
    simpa using h
  have hprev := st144_p203
  have hstep := st144_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p205 : ((6967094139289/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT144 (i+1))
      = (∑ i ∈ Finset.range 204, stT144 (i+1)) + stT144 205 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 204
    simpa using h
  have hprev := st144_p204
  have hstep := st144_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p206 : ((17448042188623/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT144 (i+1))
      = (∑ i ∈ Finset.range 205, stT144 (i+1)) + stT144 206 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 205
    simpa using h
  have hprev := st144_p205
  have hstep := st144_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p207 : ((34497777512159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT144 (i+1))
      = (∑ i ∈ Finset.range 206, stT144 (i+1)) + stT144 207 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 206
    simpa using h
  have hprev := st144_p206
  have hstep := st144_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p208 : ((33828869364447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT144 (i+1))
      = (∑ i ∈ Finset.range 207, stT144 (i+1)) + stT144 208 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 207
    simpa using h
  have hprev := st144_p207
  have hstep := st144_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p209 : ((16599187300261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT144 (i+1))
      = (∑ i ∈ Finset.range 208, stT144 (i+1)) + stT144 209 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 208
    simpa using h
  have hprev := st144_p208
  have hstep := st144_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p210 : ((16446169995223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT144 (i+1))
      = (∑ i ∈ Finset.range 209, stT144 (i+1)) + stT144 210 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 209
    simpa using h
  have hprev := st144_p209
  have hstep := st144_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p211 : ((3304566873989/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT144 (i+1))
      = (∑ i ∈ Finset.range 210, stT144 (i+1)) + stT144 211 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 210
    simpa using h
  have hprev := st144_p210
  have hstep := st144_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p212 : ((1049561467027/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT144 (i+1))
      = (∑ i ∈ Finset.range 211, stT144 (i+1)) + stT144 212 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 211
    simpa using h
  have hprev := st144_p211
  have hstep := st144_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p213 : ((4283883576397/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT144 (i+1))
      = (∑ i ∈ Finset.range 212, stT144 (i+1)) + stT144 213 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 212
    simpa using h
  have hprev := st144_p212
  have hstep := st144_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p214 : ((8699904816879/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT144 (i+1))
      = (∑ i ∈ Finset.range 213, stT144 (i+1)) + stT144 214 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 213
    simpa using h
  have hprev := st144_p213
  have hstep := st144_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p215 : ((8735876590409/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT144 (i+1))
      = (∑ i ∈ Finset.range 214, stT144 (i+1)) + stT144 215 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 214
    simpa using h
  have hprev := st144_p214
  have hstep := st144_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p216 : ((17322048152331/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT144 (i+1))
      = (∑ i ∈ Finset.range 215, stT144 (i+1)) + stT144 216 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 215
    simpa using h
  have hprev := st144_p215
  have hstep := st144_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p217 : ((17016411767981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT144 (i+1))
      = (∑ i ∈ Finset.range 216, stT144 (i+1)) + stT144 217 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 216
    simpa using h
  have hprev := st144_p216
  have hstep := st144_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p218 : ((16685332020743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT144 (i+1))
      = (∑ i ∈ Finset.range 217, stT144 (i+1)) + stT144 218 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 217
    simpa using h
  have hprev := st144_p217
  have hstep := st144_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p219 : ((2058464204833/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT144 (i+1))
      = (∑ i ∈ Finset.range 218, stT144 (i+1)) + stT144 219 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 218
    simpa using h
  have hprev := st144_p218
  have hstep := st144_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p220 : ((1028309923229/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT144 (i+1))
      = (∑ i ∈ Finset.range 219, stT144 (i+1)) + stT144 220 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 219
    simpa using h
  have hprev := st144_p219
  have hstep := st144_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p221 : ((1040339652941/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT144 (i+1))
      = (∑ i ∈ Finset.range 220, stT144 (i+1)) + stT144 221 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 220
    simpa using h
  have hprev := st144_p220
  have hstep := st144_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p222 : ((424121510169/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT144 (i+1))
      = (∑ i ∈ Finset.range 221, stT144 (i+1)) + stT144 222 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 221
    simpa using h
  have hprev := st144_p221
  have hstep := st144_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p223 : ((17280963529667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT144 (i+1))
      = (∑ i ∈ Finset.range 222, stT144 (i+1)) + stT144 223 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 222
    simpa using h
  have hprev := st144_p222
  have hstep := st144_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p224 : ((34933995407067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT144 (i+1))
      = (∑ i ∈ Finset.range 223, stT144 (i+1)) + stT144 224 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 223
    simpa using h
  have hprev := st144_p223
  have hstep := st144_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p225 : ((17450064695067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT144 (i+1))
      = (∑ i ∈ Finset.range 224, stT144 (i+1)) + stT144 225 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 224
    simpa using h
  have hprev := st144_p224
  have hstep := st144_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p226 : ((34477012703281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT144 (i+1))
      = (∑ i ∈ Finset.range 225, stT144 (i+1)) + stT144 226 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 225
    simpa using h
  have hprev := st144_p225
  have hstep := st144_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p227 : ((33833185821353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT144 (i+1))
      = (∑ i ∈ Finset.range 226, stT144 (i+1)) + stT144 227 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 226
    simpa using h
  have hprev := st144_p226
  have hstep := st144_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p228 : ((33219934526557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT144 (i+1))
      = (∑ i ∈ Finset.range 227, stT144 (i+1)) + stT144 228 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 227
    simpa using h
  have hprev := st144_p227
  have hstep := st144_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p229 : ((16436318237687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT144 (i+1))
      = (∑ i ∈ Finset.range 228, stT144 (i+1)) + stT144 229 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 228
    simpa using h
  have hprev := st144_p228
  have hstep := st144_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p230 : ((16460722550867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT144 (i+1))
      = (∑ i ∈ Finset.range 229, stT144 (i+1)) + stT144 230 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 229
    simpa using h
  have hprev := st144_p229
  have hstep := st144_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p231 : ((33344706953887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT144 (i+1))
      = (∑ i ∈ Finset.range 230, stT144 (i+1)) + stT144 231 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 230
    simpa using h
  have hprev := st144_p230
  have hstep := st144_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p232 : ((33980811617239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT144 (i+1))
      = (∑ i ∈ Finset.range 231, stT144 (i+1)) + stT144 232 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 231
    simpa using h
  have hprev := st144_p231
  have hstep := st144_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p233 : ((17295847785857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT144 (i+1))
      = (∑ i ∈ Finset.range 232, stT144 (i+1)) + stT144 233 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 232
    simpa using h
  have hprev := st144_p232
  have hstep := st144_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p234 : ((17476223188837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT144 (i+1))
      = (∑ i ∈ Finset.range 233, stT144 (i+1)) + stT144 234 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 233
    simpa using h
  have hprev := st144_p233
  have hstep := st144_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p235 : ((1746660590239/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT144 (i+1))
      = (∑ i ∈ Finset.range 234, stT144 (i+1)) + stT144 235 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 234
    simpa using h
  have hprev := st144_p234
  have hstep := st144_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p236 : ((6908792854059/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT144 (i+1))
      = (∑ i ∈ Finset.range 235, stT144 (i+1)) + stT144 236 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 235
    simpa using h
  have hprev := st144_p235
  have hstep := st144_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p237 : ((1357101777027/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT144 (i+1))
      = (∑ i ∈ Finset.range 236, stT144 (i+1)) + stT144 237 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 236
    simpa using h
  have hprev := st144_p236
  have hstep := st144_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p238 : ((33305509717563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT144 (i+1))
      = (∑ i ∈ Finset.range 237, stT144 (i+1)) + stT144 238 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 237
    simpa using h
  have hprev := st144_p237
  have hstep := st144_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p239 : ((32897879675103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT144 (i+1))
      = (∑ i ∈ Finset.range 238, stT144 (i+1)) + stT144 239 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 238
    simpa using h
  have hprev := st144_p238
  have hstep := st144_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p240 : ((6569192970591/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT144 (i+1))
      = (∑ i ∈ Finset.range 239, stT144 (i+1)) + stT144 240 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 239
    simpa using h
  have hprev := st144_p239
  have hstep := st144_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p241 : ((1326601772271/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT144 (i+1))
      = (∑ i ∈ Finset.range 240, stT144 (i+1)) + stT144 241 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 240
    simpa using h
  have hprev := st144_p240
  have hstep := st144_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p242 : ((33742087484031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT144 (i+1))
      = (∑ i ∈ Finset.range 241, stT144 (i+1)) + stT144 242 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 241
    simpa using h
  have hprev := st144_p241
  have hstep := st144_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p243 : ((34377493875531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT144 (i+1))
      = (∑ i ∈ Finset.range 242, stT144 (i+1)) + stT144 243 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 242
    simpa using h
  have hprev := st144_p242
  have hstep := st144_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p244 : ((34854953985859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT144 (i+1))
      = (∑ i ∈ Finset.range 243, stT144 (i+1)) + stT144 244 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 243
    simpa using h
  have hprev := st144_p243
  have hstep := st144_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p245 : ((7002953252351/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT144 (i+1))
      = (∑ i ∈ Finset.range 244, stT144 (i+1)) + stT144 245 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 244
    simpa using h
  have hprev := st144_p244
  have hstep := st144_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p246 : ((34805913888711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT144 (i+1))
      = (∑ i ∈ Finset.range 245, stT144 (i+1)) + stT144 246 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 245
    simpa using h
  have hprev := st144_p245
  have hstep := st144_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p247 : ((34300479626391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT144 (i+1))
      = (∑ i ∈ Finset.range 246, stT144 (i+1)) + stT144 247 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 246
    simpa using h
  have hprev := st144_p246
  have hstep := st144_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p248 : ((33667052158869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT144 (i+1))
      = (∑ i ∈ Finset.range 247, stT144 (i+1)) + stT144 248 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 247
    simpa using h
  have hprev := st144_p247
  have hstep := st144_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p249 : ((16556715316297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT144 (i+1))
      = (∑ i ∈ Finset.range 248, stT144 (i+1)) + stT144 249 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 248
    simpa using h
  have hprev := st144_p248
  have hstep := st144_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_p250 : ((16409193056929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT144 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT144 (i+1))
      = (∑ i ∈ Finset.range 249, stT144 (i+1)) + stT144 250 := by
    have h := Finset.sum_range_succ (fun i => stT144 (i+1)) 249
    simpa using h
  have hprev := st144_p249
  have hstep := st144_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st144_s250 :
    |Real.sin (((144 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))
      - ((-13821/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -5140191/10000000) (δ := 739/100000000) (ψ := -818081/1000000) 144 127
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 144`** (evaluated boundary). -/
theorem station_144_sign : hardyG ((((144:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 144 250 (by norm_num) (by norm_num)
    ((-818081/1000000 : ℚ) : ℝ)
  have hchain := st144_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT144 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((144 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-818081/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st144_c250
  have hsinb := abs_le.mp st144_s250
  have hbdy_lo : ((16140294480449/165890000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((144 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ))) / 2
          - ((((144:ℕ)):ℝ))
            * Real.sin (((144 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-818081/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((144:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((144:ℝ) * Real.log (250:ℝ) - ((-818081/1000000 : ℚ) : ℝ))) / 2
        - ((144:ℝ)) * Real.sin ((144:ℝ) * Real.log (250:ℝ) - ((-818081/1000000 : ℚ) : ℝ))
        ≥ ((127600339/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((144:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((127600339/1000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((127600339/1000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((127600339/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((144:ℕ)):ℝ))+1) * (((((144:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((90113200507/187500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((16409193056929/5000000000000 : ℚ) : ℝ) + ((16140294480449/165890000000000 : ℚ) : ℝ)
      - ((90113200507/187500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-818081/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((144:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-818081/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((144:ℕ)):ℝ)))).re
      - Real.sin ((-818081/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((144:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((144:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((144:ℕ)):ℝ))
      = (((((144:ℕ)):ℝ)) * (Real.log ((((144:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((144:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_144
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
  have hθwin : |(((-818081/1000000 : ℚ) : ℝ) + ((25:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((144:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((144:ℕ)):ℝ)))
    (φ := ((-818081/1000000 : ℚ) : ℝ) + ((25:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-818081/1000000 : ℚ) : ℝ) + ((25:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-818081/1000000 : ℚ)) : ℝ) - Real.pi) + ((25:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-818081/1000000 : ℚ)) : ℝ) - Real.pi) 25).1,
    (cos_sin_shift ((((-818081/1000000 : ℚ)) : ℝ) - Real.pi) 25).2]
  exact cos_sin_flip ((-818081/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_144_sign
end AxiomAudit
