import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 147` (rung-154.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT147 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((147 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((188437/250000 : ℚ) : ℝ))

theorem st147_c1 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((729129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -188437/1000000) (δ := 1/1000000000) (ψ := 188437/250000) 147 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t1 : ((729079/1000000 : ℚ) : ℝ) ≤ stT147 1 := by
  have hc : ((729079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((729079/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((729079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c2 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((820839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 303959/2000000) (δ := 7487/1000000000) (ψ := 188437/250000) 147 16
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t2 : ((5803854011863/10000000000000 : ℚ) : ℝ) ≤ stT147 2 := by
  have hc : ((820789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5803854011863/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((820789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c3 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-216827/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6551413/10000000) (δ := 1847/250000000) (ψ := 188437/250000) 147 26
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t3 : ((-2503847007537/5000000000000 : ℚ) : ℝ) ≤ stT147 3 := by
  have hc : ((-433679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2503847007537/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-433679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c4 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-97077/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4923979/10000000) (δ := 1843/250000000) (ψ := 188437/250000) 147 32
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t4 : ((-970895194179/5000000000000 : ℚ) : ℝ) ≤ stT147 4 := by
  have hc : ((-194179/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-970895194179/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-194179/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c5 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-977151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -57176/78125) (δ := 7529/1000000000) (ψ := 188437/250000) 147 38
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t5 : ((-546271971417/1250000000000 : ℚ) : ℝ) ≤ stT147 5 := by
  have hc : ((-977201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-546271971417/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-977201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c6 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((38359/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3147229/10000000) (δ := 7503/1000000000) (ψ := 188437/250000) 147 42
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t6 : ((313148823051/2500000000000 : ℚ) : ℝ) ≤ stT147 6 := by
  have hc : ((153411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((313148823051/2500000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((153411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c7 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-831003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6379263/10000000) (δ := 3689/500000000) (ψ := 188437/250000) 147 45
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t7 : ((-628217063237/2000000000000 : ℚ) : ℝ) ≤ stT147 7 := by
  have hc : ((-831053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-628217063237/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-831053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c8 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-491033/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7379801/10000000) (δ := 151/20000000) (ψ := 188437/250000) 147 49
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t8 : ((-434038063743/1250000000000 : ℚ) : ℝ) ≤ stT147 8 := by
  have hc : ((-245529/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-434038063743/1250000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-245529/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c9 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-2789/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 179581/400000) (δ := 1507/200000000) (ψ := 188437/250000) 147 51
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t9 : ((-37195007439/500000000000 : ℚ) : ℝ) ≤ stT147 9 := by
  have hc : ((-22317/100000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37195007439/500000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-22317/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c10 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((1261/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3914381/10000000) (δ := 3757/500000000) (ψ := 188437/250000) 147 54
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t10 : ((7896205669/5000000000000 : ℚ) : ℝ) ≤ stT147 10 := by
  have hc : ((2497/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7896205669/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((2497/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c11 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((7941/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -303809/10000000) (δ := 7499/1000000000) (ψ := 188437/250000) 147 56
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t11 : ((119709031439/400000000000 : ℚ) : ℝ) ≤ stT147 11 := by
  have hc : ((39703/40000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119709031439/400000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((39703/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c12 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((994723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 128477/5000000) (δ := 1497/200000000) (ψ := 188437/250000) 147 58
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t12 : ((2871373277423/10000000000000 : ℚ) : ℝ) ≤ stT147 12 := by
  have hc : ((994673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2871373277423/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((994673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c13 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((766571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21791/125000) (δ := 7371/1000000000) (ψ := 188437/250000) 147 60
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t13 : ((4251891987/20000000000 : ℚ) : ℝ) ≤ stT147 13 := by
  have hc : ((766521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4251891987/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((766521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c14 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-358333/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1481129/2500000) (δ := 7547/1000000000) (ψ := 188437/250000) 147 62
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t14 : ((-478876124727/2500000000000 : ℚ) : ℝ) ≤ stT147 14 := by
  have hc : ((-179179/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-478876124727/2500000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-179179/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c15 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((81741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3722411/10000000) (δ := 3677/500000000) (ψ := 188437/250000) 147 63
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t15 : ((52731295427/2500000000000 : ℚ) : ℝ) ≤ stT147 15 := by
  have hc : ((81691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52731295427/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((81691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c16 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-19449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3975617/10000000) (δ := 1487/200000000) (ψ := 188437/250000) 147 65
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t16 : ((-48747519499/10000000000000 : ℚ) : ℝ) ≤ stT147 16 := by
  have hc : ((-19499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48747519499/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-19499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c17 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((507613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 64899/250000) (δ := 941/125000000) (ψ := 188437/250000) 147 66
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t17 : ((307755241857/2500000000000 : ℚ) : ℝ) ≤ stT147 17 := by
  have hc : ((507563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((307755241857/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((507563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c18 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-499937/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3907127/5000000) (δ := 739/100000000) (ψ := 188437/250000) 147 68
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t18 : ((-589210966563/2500000000000 : ℚ) : ℝ) ≤ stT147 18 := by
  have hc : ((-249981/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-589210966563/2500000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-249981/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c19 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((1712/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3652521/10000000) (δ := 7497/1000000000) (ψ := 188437/250000) 147 69
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t19 : ((125625743163/5000000000000 : ℚ) : ℝ) ≤ stT147 19 := by
  have hc : ((54759/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125625743163/5000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((54759/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c20 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((61203/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -510197/10000000) (δ := 7399/1000000000) (ψ := 188437/250000) 147 70
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t20 : ((1094776167133/5000000000000 : ℚ) : ℝ) ≤ stT147 20 := by
  have hc : ((489599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1094776167133/5000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((489599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c21 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((154897/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 856119/5000000) (δ := 1873/250000000) (ψ := 188437/250000) 147 71
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t21 : ((168995501943/1000000000000 : ℚ) : ℝ) ≤ stT147 21 := by
  have hc : ((154887/200000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168995501943/1000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((154887/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c22 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((162327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24803/80000) (δ := 1477/200000000) (ψ := 188437/250000) 147 72
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t22 : ((173014500057/2500000000000 : ℚ) : ℝ) ≤ stT147 22 := by
  have hc : ((81151/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((173014500057/2500000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((81151/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c23 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((39667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58257/156250) (δ := 7477/1000000000) (ψ := 188437/250000) 147 73
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t23 : ((5166204903/312500000000 : ℚ) : ℝ) ≤ stT147 23 := by
  have hc : ((19821/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5166204903/312500000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((19821/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c24 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((106141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1830569/5000000) (δ := 737/100000000) (ψ := 188437/250000) 147 74
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t24 : ((216557298931/10000000000000 : ℚ) : ℝ) ≤ stT147 24 := by
  have hc : ((106091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216557298931/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((106091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c25 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((378979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 147763/500000) (δ := 93/12500000) (ψ := 188437/250000) 147 75
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t25 : ((378929/5000000 : ℚ) : ℝ) ≤ stT147 25 := by
  have hc : ((378929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((378929/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((378929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c26 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((787311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 207613/1250000) (δ := 7447/1000000000) (ψ := 188437/250000) 147 76
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t26 : ((1543945570021/10000000000000 : ℚ) : ℝ) ≤ stT147 26 := by
  have hc : ((787261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1543945570021/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((787261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c27 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((997481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -177499/10000000) (δ := 3727/500000000) (ψ := 188437/250000) 147 77
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t27 : ((3839111919/20000000000 : ℚ) : ℝ) ≤ stT147 27 := by
  have hc : ((997431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3839111919/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((997431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c28 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((533441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2520333/10000000) (δ := 7441/1000000000) (ψ := 188437/250000) 147 78
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t28 : ((504007023201/5000000000000 : ℚ) : ℝ) ≤ stT147 28 := by
  have hc : ((533391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((504007023201/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((533391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c29 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-106593/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5332243/10000000) (δ := 7469/1000000000) (ψ := 188437/250000) 147 79
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t29 : ((-98978433631/1000000000000 : ℚ) : ℝ) ≤ stT147 29 := by
  have hc : ((-106603/200000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98978433631/1000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-106603/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c30 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-478983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3563279/5000000) (δ := 7369/1000000000) (ψ := 188437/250000) 147 79
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t30 : ((-13664765999/78125000000 : ℚ) : ℝ) ≤ stT147 30 := by
  have hc : ((-14969/15625 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13664765999/78125000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-14969/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c31 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((182219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3468883/10000000) (δ := 461/62500000) (ψ := 188437/250000) 147 80
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t31 : ((327185178957/10000000000000 : ℚ) : ℝ) ≤ stT147 31 := by
  have hc : ((182169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((327185178957/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((182169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c32 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((973991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -571433/10000000) (δ := 7383/1000000000) (ψ := 188437/250000) 147 81
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t32 : ((860849892903/5000000000000 : ℚ) : ℝ) ≤ stT147 32 := by
  have hc : ((973941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((860849892903/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((973941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c33 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-40551/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4970833/10000000) (δ := 749/100000000) (ψ := 188437/250000) 147 82
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t33 : ((-17649738003/250000000000 : ℚ) : ℝ) ≤ stT147 33 := by
  have hc : ((-10139/25000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17649738003/250000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-10139/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c34 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-737433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 375009/625000) (δ := 7413/1000000000) (ψ := 188437/250000) 147 82
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t34 : ((-632386510119/5000000000000 : ℚ) : ℝ) ≤ stT147 34 := by
  have hc : ((-737483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-632386510119/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-737483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c35 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((58087/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 945087/10000000) (δ := 3703/500000000) (ψ := 188437/250000) 147 83
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t35 : ((196359277167/1250000000000 : ℚ) : ℝ) ≤ stT147 35 := by
  have hc : ((464671/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196359277167/1250000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((464671/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c36 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-192031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -441007/1000000) (δ := 1501/200000000) (ψ := 188437/250000) 147 84
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t36 : ((-320135064027/10000000000000 : ℚ) : ℝ) ≤ stT147 36 := by
  have hc : ((-192081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-320135064027/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-192081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c37 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-159679/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2829531/5000000) (δ := 3699/500000000) (ψ := 188437/250000) 147 84
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t37 : ((-52506245817/500000000000 : ℚ) : ℝ) ≤ stT147 37 := by
  have hc : ((-319383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52506245817/500000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-319383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c38 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((99507/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -124169/5000000) (δ := 7491/1000000000) (ψ := 188437/250000) 147 85
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t38 : ((40353384357/250000000000 : ℚ) : ℝ) ≤ stT147 38 := by
  have hc : ((49751/50000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40353384357/250000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((49751/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c39 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-418923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1282061/2000000) (δ := 1871/250000000) (ψ := 188437/250000) 147 86
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t39 : ((-83856736417/625000000000 : ℚ) : ℝ) ≤ stT147 39 := by
  have hc : ((-104737/125000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83856736417/625000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-104737/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c40 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((401543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2893987/10000000) (δ := 7419/1000000000) (ψ := 188437/250000) 147 86
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t40 : ((317407919517/5000000000000 : ℚ) : ℝ) ≤ stT147 40 := by
  have hc : ((401493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((317407919517/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((401493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c41 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((18737/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1869723/5000000) (δ := 7377/1000000000) (ψ := 188437/250000) 147 87
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t41 : ((58485488913/5000000000000 : ℚ) : ℝ) ≤ stT147 41 := by
  have hc : ((37449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58485488913/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((37449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c42 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-18321/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2558211/5000000) (δ := 7377/1000000000) (ψ := 188437/250000) 147 87
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t42 : ((-14136505991/200000000000 : ℚ) : ℝ) ≤ stT147 42 := by
  have hc : ((-18323/40000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14136505991/200000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-18323/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c43 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((11134/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -972041/5000000) (δ := 7533/1000000000) (ψ := 188437/250000) 147 88
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t43 : ((108659146211/1000000000000 : ℚ) : ℝ) ≤ stT147 43 := by
  have hc : ((356263/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108659146211/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((356263/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c44 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-857827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6504559/10000000) (δ := 7433/1000000000) (ψ := 188437/250000) 147 88
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t44 : ((-1293298476489/10000000000000 : ℚ) : ℝ) ≤ stT147 44 := by
  have hc : ((-857877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1293298476489/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-857877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c45 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((58091/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18893/200000) (δ := 377/50000000) (ψ := 188437/250000) 147 89
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t45 : ((692737873833/5000000000000 : ℚ) : ℝ) ≤ stT147 45 := by
  have hc : ((464703/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((692737873833/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((464703/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c46 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-14979/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1426519/2000000) (δ := 7463/1000000000) (ψ := 188437/250000) 147 89
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t46 : ((-35338382513/250000000000 : ℚ) : ℝ) ≤ stT147 46 := by
  have hc : ((-479353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35338382513/250000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-479353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c47 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((964111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -671803/10000000) (δ := 1491/200000000) (ψ := 188437/250000) 147 90
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t47 : ((1406226613589/10000000000000 : ℚ) : ℝ) ≤ stT147 47 := by
  have hc : ((964061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1406226613589/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((964061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c48 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-950653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3532661/5000000) (δ := 931/125000000) (ψ := 188437/250000) 147 90
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t48 : ((-85763868333/625000000000 : ℚ) : ℝ) ≤ stT147 48 := by
  have hc : ((-950703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85763868333/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-950703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c49 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((227653/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -532543/5000000) (δ := 1887/250000000) (ψ := 188437/250000) 147 91
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t49 : ((650401233451/5000000000000 : ℚ) : ℝ) ≤ stT147 49 := by
  have hc : ((455281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((650401233451/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((455281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c50 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-826567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6359443/10000000) (δ := 1887/250000000) (ψ := 188437/250000) 147 91
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t50 : ((-584506667019/5000000000000 : ℚ) : ℝ) ≤ stT147 50 := by
  have hc : ((-826617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-584506667019/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-826617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c51 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((676037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -258883/1250000) (δ := 3731/500000000) (ψ := 188437/250000) 147 92
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t51 : ((23664276909/250000000000 : ℚ) : ℝ) ≤ stT147 51 := by
  have hc : ((675987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23664276909/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((675987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c52 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-439677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5065087/10000000) (δ := 7541/1000000000) (ψ := 188437/250000) 147 92
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t52 : ((-609791856977/10000000000000 : ℚ) : ℝ) ≤ stT147 52 := by
  have hc : ((-439727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-609791856977/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-439727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c53 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((113487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1821331/5000000) (δ := 7469/1000000000) (ψ := 188437/250000) 147 93
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t53 : ((31163526077/2000000000000 : ℚ) : ℝ) ≤ stT147 53 := by
  have hc : ((113437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31163526077/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((113437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c54 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((138237/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 806671/2500000) (δ := 3767/500000000) (ψ := 188437/250000) 147 93
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t54 : ((47020655331/1250000000000 : ℚ) : ℝ) ≤ stT147 54 := by
  have hc : ((34553/125000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47020655331/1250000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((34553/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c55 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-165671/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1147597/2000000) (δ := 7527/1000000000) (ψ := 188437/250000) 147 94
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t55 : ((-1117038157/12500000000 : ℚ) : ℝ) ≤ stT147 55 := by
  have hc : ((-331367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1117038157/12500000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-331367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c56 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((469079/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 441907/5000000) (δ := 7427/1000000000) (ψ := 188437/250000) 147 94
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t56 : ((156699918631/1250000000000 : ℚ) : ℝ) ≤ stT147 56 := by
  have hc : ((234527/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156699918631/1250000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((234527/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c57 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-98271/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7388417/10000000) (δ := 7427/1000000000) (ψ := 188437/250000) 147 94
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t57 : ((-32542451277/250000000000 : ℚ) : ℝ) ≤ stT147 57 := by
  have hc : ((-24569/25000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32542451277/250000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-24569/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c58 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((358529/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -96403/500000) (δ := 7519/1000000000) (ψ := 188437/250000) 147 95
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t58 : ((7355292129/78125000000 : ℚ) : ℝ) ≤ stT147 58 := by
  have hc : ((44813/62500 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7355292129/78125000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((44813/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c59 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-85013/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1088533/2500000) (δ := 7519/1000000000) (ψ := 188437/250000) 147 95
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t59 : ((-5535506091/250000000000 : ℚ) : ℝ) ≤ stT147 59 := by
  have hc : ((-42519/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5535506091/250000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-42519/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c60 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-479507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2588611/5000000) (δ := 939/125000000) (ψ := 188437/250000) 147 96
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t60 : ((-123821137843/2000000000000 : ℚ) : ℝ) ≤ stT147 60 := by
  have hc : ((-479557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123821137843/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-479557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c61 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((936277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56081/625000) (δ := 1853/250000000) (ψ := 188437/250000) 147 96
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t61 : ((74919693221/625000000000 : ℚ) : ℝ) ≤ stT147 61 := by
  have hc : ((936227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74919693221/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((936227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c62 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-924001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 687303/1000000) (δ := 7391/1000000000) (ψ := 188437/250000) 147 96
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t62 : ((-586773309051/5000000000000 : ℚ) : ℝ) ≤ stT147 62 := by
  have hc : ((-924051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-586773309051/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-924051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c63 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((189577/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1477393/5000000) (δ := 3749/500000000) (ψ := 188437/250000) 147 97
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t63 : ((14925810207/312500000000 : ℚ) : ℝ) ≤ stT147 63 := by
  have hc : ((11847/31250 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14925810207/312500000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((11847/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c64 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((423867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1416357/5000000) (δ := 3699/500000000) (ψ := 188437/250000) 147 97
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t64 : ((423817/8000000 : ℚ) : ℝ) ≤ stT147 64 := by
  have hc : ((423817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((423817/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((423817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c65 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-120451/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -448591/625000) (δ := 3699/500000000) (ψ := 188437/250000) 147 98
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t65 : ((-149408909123/1250000000000 : ℚ) : ℝ) ≤ stT147 65 := by
  have hc : ((-481829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149408909123/1250000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-481829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c66 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((809991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -31333/200000) (δ := 3749/500000000) (ψ := 188437/250000) 147 98
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t66 : ((498483858037/5000000000000 : ℚ) : ℝ) ≤ stT147 66 := by
  have hc : ((809941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((498483858037/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((809941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c67 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-2623/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3959779/10000000) (δ := 1501/200000000) (ψ := 188437/250000) 147 98
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t67 : ((-643344587/400000000000 : ℚ) : ℝ) ≤ stT147 67 := by
  have hc : ((-2633/200000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-643344587/400000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-2633/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c68 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-406899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1260727/2000000) (δ := 939/125000000) (ψ := 188437/250000) 147 99
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t68 : ((-123367047349/1250000000000 : ℚ) : ℝ) ≤ stT147 68 := by
  have hc : ((-101731/125000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123367047349/1250000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-101731/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c69 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((18607/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58661/625000) (δ := 939/125000000) (ψ := 188437/250000) 147 99
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t69 : ((5599745487/50000000000 : ℚ) : ℝ) ≤ stT147 69 := by
  have hc : ((9303/10000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5599745487/50000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((9303/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c70 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-16811/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4349271/10000000) (δ := 1853/250000000) (ψ := 188437/250000) 147 99
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t70 : ((-1256185679/62500000000 : ℚ) : ℝ) ≤ stT147 70 := by
  have hc : ((-1051/6250 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1256185679/62500000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-1051/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c71 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-193881/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1536463/2500000) (δ := 923/125000000) (ψ := 188437/250000) 147 100
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t71 : ((-230109315717/2500000000000 : ℚ) : ℝ) ≤ stT147 71 := by
  have hc : ((-387787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230109315717/2500000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-387787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c72 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((920141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1005887/10000000) (δ := 1871/250000000) (ψ := 188437/250000) 147 100
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t72 : ((1084337364501/10000000000000 : ℚ) : ℝ) ≤ stT147 72 := by
  have hc : ((920091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1084337364501/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((920091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c73 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-54437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4063151/10000000) (δ := 923/125000000) (ψ := 188437/250000) 147 100
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t73 : ((-15943059661/2500000000000 : ℚ) : ℝ) ≤ stT147 73 := by
  have hc : ((-54487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15943059661/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-54487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c74 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-221321/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3322377/5000000) (δ := 7427/1000000000) (ψ := 188437/250000) 147 101
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t74 : ((-514590206159/5000000000000 : ℚ) : ℝ) ≤ stT147 74 := by
  have hc : ((-442667/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-514590206159/5000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-442667/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c75 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((154921/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -342353/2000000) (δ := 461/62500000) (ψ := 188437/250000) 147 101
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t75 : ((1788757317/20000000000 : ℚ) : ℝ) ≤ stT147 75 := by
  have hc : ((154911/200000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1788757317/20000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((154911/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c76 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((30359/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1577923/5000000) (δ := 461/62500000) (ψ := 188437/250000) 147 101
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t76 : ((8704601403/250000000000 : ℚ) : ℝ) ≤ stT147 76 := by
  have hc : ((15177/50000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8704601403/250000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((15177/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c77 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-15611/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -193703/250000) (δ := 3767/500000000) (ψ := 188437/250000) 147 102
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t77 : ((-284660473331/2500000000000 : ℚ) : ℝ) ≤ stT147 77 := by
  have hc : ((-499577/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284660473331/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-499577/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c78 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((14403/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3006121/10000000) (δ := 7369/1000000000) (ψ := 188437/250000) 147 102
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t78 : ((16305921077/400000000000 : ℚ) : ℝ) ≤ stT147 78 := by
  have hc : ((14401/40000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16305921077/400000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((14401/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c79 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((783707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 837731/5000000) (δ := 3767/500000000) (ψ := 188437/250000) 147 102
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t79 : ((881682303159/10000000000000 : ℚ) : ℝ) ≤ stT147 79 := by
  have hc : ((783657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((881682303159/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((783657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c80 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-406263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6298171/10000000) (δ := 3767/500000000) (ψ := 188437/250000) 147 102
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t80 : ((-14195118681/156250000000 : ℚ) : ℝ) ≤ stT147 80 := by
  have hc : ((-25393/31250 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14195118681/156250000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-25393/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c81 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-358829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1211131/2500000) (δ := 3681/500000000) (ψ := 188437/250000) 147 103
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t81 : ((-49844345431/1250000000000 : ℚ) : ℝ) ≤ stT147 81 := by
  have hc : ((-358879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49844345431/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-358879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c82 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((991021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -167631/5000000) (δ := 7441/1000000000) (ψ := 188437/250000) 147 103
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t82 : ((218868827973/2000000000000 : ℚ) : ℝ) ≤ stT147 82 := by
  have hc : ((990971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218868827973/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((990971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c83 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-76869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 514919/1250000) (δ := 3731/500000000) (ψ := 188437/250000) 147 103
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t83 : ((-84429601917/10000000000000 : ℚ) : ℝ) ≤ stT147 83 := by
  have hc : ((-76919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84429601917/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-76919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c84 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-964661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -449211/625000) (δ := 2951/200000000) (ψ := 188437/250000) 147 104
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t84 : ((-105258652499/1000000000000 : ℚ) : ℝ) ≤ stT147 84 := by
  have hc : ((-964711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105258652499/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-964711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c85 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((421873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -567643/2000000) (δ := 1887/250000000) (ψ := 188437/250000) 147 104
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t85 : ((114382790149/2500000000000 : ℚ) : ℝ) ≤ stT147 85 := by
  have hc : ((421823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114382790149/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((421823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c86 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((3337/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 292013/2000000) (δ := 1887/250000000) (ψ := 188437/250000) 147 104
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t86 : ((4497701917/50000000000 : ℚ) : ℝ) ≤ stT147 86 := by
  have hc : ((4171/5000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4497701917/50000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((4171/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c87 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-130773/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1141739/2000000) (δ := 1491/200000000) (ψ := 188437/250000) 147 104
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t87 : ((-140214154479/2000000000000 : ℚ) : ℝ) ≤ stT147 87 := by
  have hc : ((-130783/200000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140214154479/2000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-130783/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c88 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-170207/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5799221/10000000) (δ := 931/125000000) (ψ := 188437/250000) 147 105
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t88 : ((-90727333939/1250000000000 : ℚ) : ℝ) ≤ stT147 88 := by
  have hc : ((-340439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90727333939/1250000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-340439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c89 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((197703/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -329331/2000000) (δ := 1887/250000000) (ψ := 188437/250000) 147 105
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t89 : ((419102673857/5000000000000 : ℚ) : ℝ) ≤ stT147 89 := by
  have hc : ((395381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((419102673857/5000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((395381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c90 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((138463/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2459533/10000000) (δ := 931/125000000) (ψ := 188437/250000) 147 105
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t90 : ((72969782223/1250000000000 : ℚ) : ℝ) ≤ stT147 90 := by
  have hc : ((276901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72969782223/1250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((276901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c91 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-861057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6520353/10000000) (δ := 3687/250000000) (ψ := 188437/250000) 147 105
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t91 : ((-180537110299/2000000000000 : ℚ) : ℝ) ≤ stT147 91 := by
  have hc : ((-861107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180537110299/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-861107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c92 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-238693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -323199/625000) (δ := 7463/1000000000) (ψ := 188437/250000) 147 106
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t92 : ((-124440470707/2500000000000 : ℚ) : ℝ) ≤ stT147 92 := by
  have hc : ((-119359/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124440470707/2500000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-119359/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c93 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((887331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1198179/10000000) (δ := 377/50000000) (ψ := 188437/250000) 147 106
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t93 : ((920066920231/10000000000000 : ℚ) : ℝ) ≤ stT147 93 := by
  have hc : ((887281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((920066920231/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((887281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c94 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((459879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 341543/1250000) (δ := 93/12500000) (ψ := 188437/250000) 147 106
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t94 : ((474277287009/10000000000000 : ℚ) : ℝ) ≤ stT147 94 := by
  have hc : ((459829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((474277287009/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((459829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c95 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-220219/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3310633/5000000) (δ := 7363/1000000000) (ψ := 188437/250000) 147 106
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t95 : ((-451905788277/5000000000000 : ℚ) : ℝ) ≤ stT147 95 := by
  have hc : ((-440463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-451905788277/5000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-440463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c96 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-125217/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1047699/2000000) (δ := 7533/1000000000) (ψ := 188437/250000) 147 107
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t96 : ((-255623715039/5000000000000 : ℚ) : ℝ) ≤ stT147 96 := by
  have hc : ((-250459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-255623715039/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-250459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c97 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((52549/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -715083/5000000) (δ := 7533/1000000000) (ψ := 188437/250000) 147 107
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t97 : ((213408975991/2500000000000 : ℚ) : ℝ) ≤ stT147 97 := by
  have hc : ((420367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213408975991/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((420367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c98 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((74163/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1169549/5000000) (δ := 7433/1000000000) (ψ := 188437/250000) 147 107
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t98 : ((37454794663/625000000000 : ℚ) : ℝ) ≤ stT147 98 := by
  have hc : ((296627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37454794663/625000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((296627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c99 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-756043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1214021/2000000) (δ := 7433/1000000000) (ψ := 188437/250000) 147 107
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t99 : ((-379951098267/5000000000000 : ℚ) : ℝ) ≤ stT147 99 := by
  have hc : ((-756093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-379951098267/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-756093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c100 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-722183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5944373/10000000) (δ := 3713/500000000) (ψ := 188437/250000) 147 108
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t100 : ((-722233/10000000 : ℚ) : ℝ) ≤ stT147 100 := by
  have hc : ((-722233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-722233/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-722233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c101 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((609759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2287601/10000000) (δ := 3713/500000000) (ψ := 188437/250000) 147 108
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t101 : ((606683014233/10000000000000 : ℚ) : ℝ) ≤ stT147 101 := by
  have hc : ((609709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((606683014233/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((609709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c102 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((861161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1333119/10000000) (δ := 3763/500000000) (ψ := 188437/250000) 147 108
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t102 : ((852626473317/10000000000000 : ℚ) : ℝ) ≤ stT147 102 := by
  have hc : ((861111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((852626473317/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((861111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c103 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-386283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2459243/5000000) (δ := 3713/500000000) (ψ := 188437/250000) 147 108
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t103 : ((-38066549489/1000000000000 : ℚ) : ℝ) ≤ stT147 103 := by
  have hc : ((-386333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38066549489/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-386333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c104 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-96987/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7238729/10000000) (δ := 7419/1000000000) (ψ := 188437/250000) 147 109
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t104 : ((-2972141011/31250000000 : ℚ) : ℝ) ≤ stT147 104 := by
  have hc : ((-3031/3125 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2972141011/31250000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-3031/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c105 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((81929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1860969/5000000) (δ := 7519/1000000000) (ψ := 188437/250000) 147 109
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t105 : ((799057161/100000000000 : ℚ) : ℝ) ≤ stT147 105 := by
  have hc : ((81879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((799057161/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((81879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c106 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((248863/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47703/2000000) (δ := 1871/250000000) (ψ := 188437/250000) 147 109
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t106 : ((96681903157/1000000000000 : ℚ) : ℝ) ≤ stT147 106 := by
  have hc : ((497701/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96681903157/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((497701/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c107 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((282023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 803059/2500000) (δ := 7419/1000000000) (ψ := 188437/250000) 147 109
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t107 : ((17037090633/625000000000 : ℚ) : ℝ) ≤ stT147 107 := by
  have hc : ((281973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17037090633/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((281973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c108 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-13792/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1657717/2500000) (δ := 7419/1000000000) (ψ := 188437/250000) 147 109
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t108 : ((-424707761619/5000000000000 : ℚ) : ℝ) ≤ stT147 108 := by
  have hc : ((-441369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-424707761619/5000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-441369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c109 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-648187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1137999/2000000) (δ := 939/125000000) (ψ := 188437/250000) 147 110
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t109 : ((-620898900999/10000000000000 : ℚ) : ℝ) ≤ stT147 109 := by
  have hc : ((-648237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-620898900999/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-648237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c110 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((9297/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2333801/10000000) (δ := 1853/250000000) (ψ := 188437/250000) 147 110
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t110 : ((141817461149/2500000000000 : ℚ) : ℝ) ≤ stT147 110 := by
  have hc : ((297479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141817461149/2500000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((297479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c111 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((922297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 992037/10000000) (δ := 939/125000000) (ψ := 188437/250000) 147 110
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t111 : ((875357195779/10000000000000 : ℚ) : ℝ) ≤ stT147 111 := by
  have hc : ((922247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((875357195779/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((922247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c112 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-71951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2143999/5000000) (δ := 7391/1000000000) (ψ := 188437/250000) 147 110
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t112 : ((-531335829/39062500000 : ℚ) : ℝ) ≤ stT147 112 := by
  have hc : ((-8997/62500 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-531335829/39062500000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-8997/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c113 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-992843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1510941/2000000) (δ := 939/125000000) (ψ := 188437/250000) 147 110
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t113 : ((-934035295853/10000000000000 : ℚ) : ℝ) ≤ stT147 113 := by
  have hc : ((-992893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-934035295853/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-992893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c114 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-38513/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2457681/5000000) (δ := 3749/500000000) (ψ := 188437/250000) 147 111
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t114 : ((-9018854887/250000000000 : ℚ) : ℝ) ≤ stT147 114 := by
  have hc : ((-19259/50000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9018854887/250000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-19259/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c115 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((77613/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13326/78125) (δ := 1501/200000000) (ψ := 188437/250000) 147 111
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t115 : ((1130777663/15625000000 : ℚ) : ℝ) ≤ stT147 115 := by
  have hc : ((9701/12500 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1130777663/15625000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((9701/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c116 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((830699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1476087/10000000) (δ := 1501/200000000) (ψ := 188437/250000) 147 111
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t116 : ((192809415231/2500000000000 : ℚ) : ℝ) ≤ stT147 116 := by
  have hc : ((830649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192809415231/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((830649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c117 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-69439/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2315317/5000000) (δ := 3699/500000000) (ψ := 188437/250000) 147 111
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t117 : ((-128415962403/5000000000000 : ℚ) : ℝ) ≤ stT147 117 := by
  have hc : ((-138903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128415962403/5000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-138903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c118 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-249817/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1939579/2500000) (δ := 1481/200000000) (ψ := 188437/250000) 147 111
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t118 : ((-18398943357/200000000000 : ℚ) : ℝ) ≤ stT147 118 := by
  have hc : ((-499659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18398943357/200000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-499659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c119 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-360271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1212097/2500000) (δ := 3703/500000000) (ψ := 188437/250000) 147 112
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t119 : ((-330305900379/10000000000000 : ℚ) : ℝ) ≤ stT147 119 := by
  have hc : ((-360321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-330305900379/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-360321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c120 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((758873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -886519/5000000) (δ := 7397/1000000000) (ψ := 188437/250000) 147 112
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t120 : ((69270675201/1000000000000 : ℚ) : ℝ) ≤ stT147 120 := by
  have hc : ((758823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69270675201/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((758823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c121 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((436199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1276771/10000000) (δ := 7397/1000000000) (ψ := 188437/250000) 147 112
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t121 : ((19826071083/250000000000 : ℚ) : ℝ) ≤ stT147 121 := by
  have hc : ((218087/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19826071083/250000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((218087/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c122 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-37309/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 107537/250000) (δ := 3703/500000000) (ψ := 188437/250000) 147 112
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t122 : ((-33789318597/2500000000000 : ℚ) : ℝ) ≤ stT147 122 := by
  have hc : ((-74643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33789318597/2500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-74643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c123 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-3049/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7301493/10000000) (δ := 3753/500000000) (ψ := 188437/250000) 147 112
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t123 : ((-8797864691/100000000000 : ℚ) : ℝ) ≤ stT147 123 := by
  have hc : ((-97573/100000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8797864691/100000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-97573/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c124 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-565883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21723/40000) (δ := 749/100000000) (ψ := 188437/250000) 147 113
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t124 : ((-508223114191/10000000000000 : ℚ) : ℝ) ≤ stT147 124 := by
  have hc : ((-565933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-508223114191/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-565933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c125 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((27369/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -619729/2500000) (δ := 7413/1000000000) (ψ := 188437/250000) 147 113
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t125 : ((48954672991/1000000000000 : ℚ) : ℝ) ≤ stT147 125 := by
  have hc : ((54733/100000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48954672991/1000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((54733/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c126 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((983887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 449397/10000000) (δ := 749/100000000) (ψ := 188437/250000) 147 113
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t126 : ((87647086819/1000000000000 : ℚ) : ℝ) ≤ stT147 126 := by
  have hc : ((983837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87647086819/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((983837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c127 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((14187/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1677261/5000000) (δ := 7513/1000000000) (ψ := 188437/250000) 147 113
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t127 : ((25172293169/1250000000000 : ℚ) : ℝ) ≤ stT147 127 := by
  have hc : ((113471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25172293169/1250000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((113471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c128 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-199499/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3118449/5000000) (δ := 7513/1000000000) (ψ := 188437/250000) 147 113
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t128 : ((-88172511333/1250000000000 : ℚ) : ℝ) ≤ stT147 128 := by
  have hc : ((-399023/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88172511333/1250000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-399023/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c129 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-175789/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6611107/10000000) (δ := 371/50000000) (ψ := 188437/250000) 147 114
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t129 : ((-154782405349/2000000000000 : ℚ) : ℝ) ≤ stT147 129 := by
  have hc : ((-175799/200000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154782405349/2000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-175799/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c130 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((61449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -471659/1250000) (δ := 371/50000000) (ψ := 188437/250000) 147 114
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t130 : ((26925242071/5000000000000 : ℚ) : ℝ) ≤ stT147 130 := by
  have hc : ((61399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26925242071/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((61399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c131 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((927599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -239289/2500000) (δ := 47/6250000) (ψ := 188437/250000) 147 114
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t131 : ((101300408937/1250000000000 : ℚ) : ℝ) ≤ stT147 131 := by
  have hc : ((927549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101300408937/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((927549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c132 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((370911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 918767/5000000) (δ := 7383/1000000000) (ψ := 188437/250000) 147 114
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t132 : ((40351840471/625000000000 : ℚ) : ℝ) ≤ stT147 132 := by
  have hc : ((185443/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40351840471/625000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((185443/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c133 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-270253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 461113/1000000) (δ := 7383/1000000000) (ψ := 188437/250000) 147 114
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t133 : ((-23438243433/1000000000000 : ℚ) : ℝ) ≤ stT147 133 := by
  have hc : ((-270303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23438243433/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-270303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c134 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-19617/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 920493/1250000) (δ := 23/1562500) (ψ := 188437/250000) 147 114
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t134 : ((-8473691021/100000000000 : ℚ) : ℝ) ≤ stT147 134 := by
  have hc : ((-9809/10000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8473691021/100000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-9809/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c135 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-312009/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -224467/400000) (δ := 7427/1000000000) (ψ := 188437/250000) 147 115
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t135 : ((-134278059271/2500000000000 : ℚ) : ℝ) ≤ stT147 135 := by
  have hc : ((-156017/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134278059271/2500000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-156017/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c136 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((399527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -90609/312500) (δ := 7527/1000000000) (ψ := 188437/250000) 147 115
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t136 : ((85637082921/2500000000000 : ℚ) : ℝ) ≤ stT147 136 := by
  have hc : ((399477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85637082921/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((399477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c137 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((996569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -207147/10000000) (δ := 1869/250000000) (ψ := 188437/250000) 147 115
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t137 : ((851382983283/10000000000000 : ℚ) : ℝ) ≤ stT147 137 := by
  have hc : ((996519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((851382983283/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((996519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c138 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((551839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2465571/10000000) (δ := 7527/1000000000) (ψ := 188437/250000) 147 115
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t138 : ((58714212123/1250000000000 : ℚ) : ℝ) ≤ stT147 138 := by
  have hc : ((551789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58714212123/1250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((551789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c139 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-458953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5119031/10000000) (δ := 7427/1000000000) (ψ := 188437/250000) 147 115
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t139 : ((-389321295567/10000000000000 : ℚ) : ℝ) ≤ stT147 139 := by
  have hc : ((-459003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-389321295567/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-459003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c140 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-124899/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1550691/2000000) (δ := 7527/1000000000) (ψ := 188437/250000) 147 115
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t140 : ((-84451437251/1000000000000 : ℚ) : ℝ) ≤ stT147 140 := by
  have hc : ((-499621/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84451437251/1000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-499621/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c141 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-133801/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -333679/625000) (δ := 3717/500000000) (ψ := 188437/250000) 147 116
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t141 : ((-28172826663/625000000000 : ℚ) : ℝ) ≤ stT147 141 := by
  have hc : ((-267627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28172826663/625000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-267627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c142 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((114141/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -685417/2500000) (δ := 3717/500000000) (ψ := 188437/250000) 147 116
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t142 : ((191548937517/5000000000000 : ℚ) : ℝ) ≤ stT147 142 := by
  have hc : ((228257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191548937517/5000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((228257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c143 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((997883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1627/100000) (δ := 3717/500000000) (ψ := 188437/250000) 147 116
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t143 : ((417214931793/5000000000000 : ℚ) : ℝ) ≤ stT147 143 := by
  have hc : ((997833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((417214931793/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((997833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c144 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((57409/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119913/500000) (δ := 7469/1000000000) (ψ := 188437/250000) 147 116
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t144 : ((11959161883/250000000000 : ℚ) : ℝ) ≤ stT147 144 := by
  have hc : ((14351/25000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11959161883/250000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((14351/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c145 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-394773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 617693/1250000) (δ := 7369/1000000000) (ψ := 188437/250000) 147 116
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t145 : ((-65576546893/2000000000000 : ℚ) : ℝ) ≤ stT147 145 := by
  have hc : ((-394823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65576546893/2000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-394823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c146 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-30877/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1493467/2000000) (δ := 3717/500000000) (ψ := 188437/250000) 147 116
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t146 : ((-204442268771/2500000000000 : ℚ) : ℝ) ≤ stT147 146 := by
  have hc : ((-494057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204442268771/2500000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-494057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c147 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-660923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -573211/1000000) (δ := 3721/500000000) (ψ := 188437/250000) 147 117
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t147 : ((-545161937751/10000000000000 : ℚ) : ℝ) ≤ stT147 147 := by
  have hc : ((-660973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-545161937751/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-660973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c148 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((271131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -324057/1000000) (δ := 3771/500000000) (ψ := 188437/250000) 147 117
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t148 : ((111413477757/5000000000000 : ℚ) : ℝ) ≤ stT147 148 := by
  have hc : ((271081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111413477757/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((271081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c149 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((953451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -765789/10000000) (δ := 7461/1000000000) (ψ := 188437/250000) 147 117
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t149 : ((781055654631/10000000000000 : ℚ) : ℝ) ≤ stT147 149 := by
  have hc : ((953401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((781055654631/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((953401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c150 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((155897/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 846191/5000000) (δ := 7361/1000000000) (ψ := 188437/250000) 147 117
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t150 : ((7955069497/125000000000 : ℚ) : ℝ) ≤ stT147 150 := by
  have hc : ((155887/200000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7955069497/125000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((155887/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c151 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-41409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4134273/10000000) (δ := 3771/500000000) (ψ := 188437/250000) 147 117
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t151 : ((-16859266713/2500000000000 : ℚ) : ℝ) ≤ stT147 151 := by
  have hc : ((-20717/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16859266713/2500000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-20717/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c152 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-869019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 656003/1000000) (δ := 3721/500000000) (ψ := 188437/250000) 147 117
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t152 : ((-176227204613/2500000000000 : ℚ) : ℝ) ≤ stT147 152 := by
  have hc : ((-869069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176227204613/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-869069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c153 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-451013/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6738089/10000000) (δ := 3677/500000000) (ψ := 188437/250000) 147 118
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t153 : ((-182321512107/2500000000000 : ℚ) : ℝ) ≤ stT147 153 := by
  have hc : ((-225519/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182321512107/2500000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-225519/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c154 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-83003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4343937/10000000) (δ := 3727/500000000) (ψ := 188437/250000) 147 118
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t154 : ((-16726468011/1250000000000 : ℚ) : ℝ) ≤ stT147 154 := by
  have hc : ((-20757/125000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16726468011/1250000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-20757/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c155 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((353299/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1965293/10000000) (δ := 3677/500000000) (ψ := 188437/250000) 147 118
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t155 : ((141878194503/2500000000000 : ℚ) : ℝ) ≤ stT147 155 := by
  have hc : ((176637/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141878194503/2500000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((176637/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c156 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((19747/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 398063/10000000) (δ := 7449/1000000000) (ψ := 188437/250000) 147 118
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t156 : ((12351123/156250000 : ℚ) : ℝ) ≤ stT147 156 := by
  have hc : ((9873/10000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12351123/156250000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((9873/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c157 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((45491/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1373157/5000000) (δ := 3727/500000000) (ψ := 188437/250000) 147 118
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t157 : ((9075434949/250000000000 : ℚ) : ℝ) ≤ stT147 157 := by
  have hc : ((22743/50000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9075434949/250000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((22743/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c158 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-444899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1015929/2000000) (δ := 3727/500000000) (ψ := 188437/250000) 147 118
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t158 : ((-176991368271/5000000000000 : ℚ) : ℝ) ≤ stT147 158 := by
  have hc : ((-444949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176991368271/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-444949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c159 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-983433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1849569/2500000) (δ := 3727/500000000) (ψ := 188437/250000) 147 118
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t159 : ((-194988290029/2500000000000 : ℚ) : ℝ) ≤ stT147 159 := by
  have hc : ((-983483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194988290029/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-983483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c160 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-738907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6005609/10000000) (δ := 1839/250000000) (ψ := 188437/250000) 147 119
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t160 : ((-58419723549/1000000000000 : ℚ) : ℝ) ≤ stT147 160 := by
  have hc : ((-738957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58419723549/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-738957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c161 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((5271/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37159/100000) (δ := 233/31250000) (ψ := 188437/250000) 147 119
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t161 : ((3321331973/500000000000 : ℚ) : ℝ) ≤ stT147 161 := by
  have hc : ((42143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3321331973/500000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((42143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c162 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((419287/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72017/500000) (δ := 233/31250000) (ψ := 188437/250000) 147 119
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t162 : ((82350813147/1250000000000 : ℚ) : ℝ) ≤ stT147 162 := by
  have hc : ((209631/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82350813147/1250000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((209631/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c163 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((946531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 410609/5000000) (δ := 1839/250000000) (ψ := 188437/250000) 147 119
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t163 : ((37067035403/500000000000 : ℚ) : ℝ) ≤ stT147 163 := by
  have hc : ((946481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37067035403/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((946481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c164 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((21033/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3068921/10000000) (δ := 7547/1000000000) (ψ := 188437/250000) 147 119
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t164 : ((32843112863/1250000000000 : ℚ) : ℝ) ≤ stT147 164 := by
  have hc : ((168239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32843112863/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((168239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c165 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-65377/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2651477/5000000) (δ := 1839/250000000) (ψ := 188437/250000) 147 119
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t165 : ((-203603178967/5000000000000 : ℚ) : ℝ) ≤ stT147 165 := by
  have hc : ((-261533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-203603178967/5000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-261533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c166 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-39651/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7523499/10000000) (δ := 7447/1000000000) (ψ := 188437/250000) 147 119
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t166 : ((-30776715603/400000000000 : ℚ) : ℝ) ≤ stT147 166 := by
  have hc : ((-39653/40000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30776715603/400000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-39653/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c167 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-731209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2988611/5000000) (δ := 7463/1000000000) (ψ := 188437/250000) 147 120
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t167 : ((-8841652569/156250000000 : ℚ) : ℝ) ≤ stT147 167 := by
  have hc : ((-731259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8841652569/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-731259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c168 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((1437/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3783211/10000000) (δ := 377/50000000) (ψ := 188437/250000) 147 120
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t168 : ((1107704097/250000000000 : ℚ) : ℝ) ≤ stT147 168 := by
  have hc : ((5743/100000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1107704097/250000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((5743/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c169 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((801577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -400543/2500000) (δ := 377/50000000) (ψ := 188437/250000) 147 120
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t169 : ((61655861421/1000000000000 : ℚ) : ℝ) ≤ stT147 169 := by
  have hc : ((801527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61655861421/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((801527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c170 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((243621/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 35373/625000) (δ := 93/12500000) (ψ := 188437/250000) 147 120
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t170 : ((93419474797/1250000000000 : ℚ) : ℝ) ≤ stT147 170 := by
  have hc : ((487217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93419474797/1250000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((487217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c171 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((115941/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 170087/625000) (δ := 377/50000000) (ψ := 188437/250000) 147 120
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t171 : ((177305453183/5000000000000 : ℚ) : ℝ) ≤ stT147 171 := by
  have hc : ((231857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177305453183/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((231857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c172 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-183091/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 608031/1250000) (δ := 93/12500000) (ψ := 188437/250000) 147 120
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t172 : ((-34906167047/1250000000000 : ℚ) : ℝ) ≤ stT147 172 := by
  have hc : ((-45779/125000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34906167047/1250000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-45779/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c173 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-235377/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3497341/5000000) (δ := 377/50000000) (ψ := 188437/250000) 147 120
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t173 : ((-178963341397/2500000000000 : ℚ) : ℝ) ≤ stT147 173 := by
  have hc : ((-470779/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178963341397/2500000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-470779/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c174 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-437939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6595121/10000000) (δ := 737/100000000) (ψ := 188437/250000) 147 121
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t174 : ((-83005017609/1250000000000 : ℚ) : ℝ) ≤ stT147 174 := by
  have hc : ((-109491/125000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83005017609/1250000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-109491/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c175 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-4459/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4489089/10000000) (δ := 7433/1000000000) (ψ := 188437/250000) 147 121
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t175 : ((-168572167/10000000000 : ℚ) : ℝ) ≤ stT147 175 := by
  have hc : ((-223/1000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168572167/10000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-223/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c176 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((575133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1197537/5000000) (δ := 7433/1000000000) (ψ := 188437/250000) 147 121
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t176 : ((216742456787/5000000000000 : ℚ) : ℝ) ≤ stT147 176 := by
  have hc : ((575083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216742456787/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((575083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c177 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((496089/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -78223/2500000) (δ := 747/100000000) (ψ := 188437/250000) 147 121
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t177 : ((2913004073/39062500000 : ℚ) : ℝ) ≤ stT147 177 := by
  have hc : ((15502/15625 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2913004073/39062500000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((15502/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c178 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((762899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1757529/10000000) (δ := 7433/1000000000) (ψ := 188437/250000) 147 121
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t178 : ((571778973819/10000000000000 : ℚ) : ℝ) ≤ stT147 178 := by
  have hc : ((762849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((571778973819/10000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((762849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c179 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((5529/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1908187/5000000) (δ := 7533/1000000000) (ψ := 188437/250000) 147 121
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t179 : ((3302317317/1000000000000 : ℚ) : ℝ) ≤ stT147 179 := by
  have hc : ((22091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3302317317/1000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((22091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c180 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-139899/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5863717/10000000) (δ := 737/100000000) (ψ := 188437/250000) 147 121
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t180 : ((-26070503151/500000000000 : ℚ) : ℝ) ≤ stT147 180 := by
  have hc : ((-139909/200000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26070503151/500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-139909/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c181 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-124979/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7808223/10000000) (δ := 3713/500000000) (ψ := 188437/250000) 147 122
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t181 : ((-74320729119/1000000000000 : ℚ) : ℝ) ≤ stT147 181 := by
  have hc : ((-499941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74320729119/1000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-499941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c182 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-21131/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1156689/2000000) (δ := 3713/500000000) (ψ := 188437/250000) 147 122
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t182 : ((-200505753/4000000000 : ℚ) : ℝ) ≤ stT147 182 := by
  have hc : ((-338121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-200505753/4000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-338121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c183 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((62863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3769729/10000000) (δ := 3763/500000000) (ψ := 188437/250000) 147 122
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t183 : ((46432688673/10000000000000 : ℚ) : ℝ) ≤ stT147 183 := by
  have hc : ((62813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46432688673/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((62813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c184 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((190111/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1767001/10000000) (δ := 3763/500000000) (ψ := 188437/250000) 147 122
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t184 : ((280284650173/5000000000000 : ℚ) : ℝ) ≤ stT147 184 := by
  have hc : ((380197/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((280284650173/5000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((380197/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c185 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((995957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 112443/5000000) (δ := 3713/500000000) (ψ := 188437/250000) 147 122
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t185 : ((366102384549/5000000000000 : ℚ) : ℝ) ≤ stT147 185 := by
  have hc : ((995907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((366102384549/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((995907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c186 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((317649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 441201/2000000) (δ := 3713/500000000) (ψ := 188437/250000) 147 122
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t186 : ((5822325841/125000000000 : ℚ) : ℝ) ≤ stT147 186 := by
  have hc : ((39703/62500 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5822325841/125000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((39703/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c187 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-49827/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 208827/500000) (δ := 3713/500000000) (ψ := 188437/250000) 147 122
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t187 : ((-9113855399/1250000000000 : ℚ) : ℝ) ≤ stT147 187 := by
  have hc : ((-12463/125000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9113855399/1250000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-12463/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c188 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-193291/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 383533/625000) (δ := 7377/1000000000) (ψ := 188437/250000) 147 122
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t188 : ((-11278486011/200000000000 : ℚ) : ℝ) ≤ stT147 188 := by
  have hc : ((-386607/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11278486011/200000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-386607/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c189 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-995691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7621811/10000000) (δ := 1477/200000000) (ψ := 188437/250000) 147 123
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t189 : ((-724295033213/10000000000000 : ℚ) : ℝ) ≤ stT147 189 := by
  have hc : ((-995741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-724295033213/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-995741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c190 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-322953/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2841257/5000000) (δ := 3759/500000000) (ψ := 188437/250000) 147 123
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t190 : ((-117156555253/2500000000000 : ℚ) : ℝ) ≤ stT147 190 := by
  have hc : ((-161489/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117156555253/2500000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-161489/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c191 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((69397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3753359/10000000) (δ := 1477/200000000) (ψ := 188437/250000) 147 123
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t191 : ((25088843089/5000000000000 : ℚ) : ℝ) ≤ stT147 191 := by
  have hc : ((69347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25088843089/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((69347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c192 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((371343/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1834311/10000000) (δ := 3709/500000000) (ψ := 188437/250000) 147 123
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t192 : ((133987686733/2500000000000 : ℚ) : ℝ) ≤ stT147 192 := by
  have hc : ((185659/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133987686733/2500000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((185659/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c193 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((999553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 37389/5000000) (δ := 3709/500000000) (ψ := 188437/250000) 147 123
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t193 : ((143891450389/2000000000000 : ℚ) : ℝ) ≤ stT147 193 := by
  have hc : ((999503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143891450389/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((999503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c194 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((176031/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 987009/5000000) (δ := 3709/500000000) (ψ := 188437/250000) 147 123
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t194 : ((126373890223/2500000000000 : ℚ) : ℝ) ≤ stT147 194 := by
  have hc : ((352037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126373890223/2500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((352037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c195 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((127/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3863483/10000000) (δ := 1497/200000000) (ψ := 188437/250000) 147 123
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t195 : ((181534899/100000000000 : ℚ) : ℝ) ≤ stT147 195 := by
  have hc : ((507/20000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181534899/100000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((507/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c196 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-66427/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2871641/5000000) (δ := 1477/200000000) (ψ := 188437/250000) 147 123
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t196 : ((-185357217/3906250000 : ℚ) : ℝ) ≤ stT147 196 := by
  have hc : ((-2076/3125 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185357217/3906250000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-2076/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c197 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-497689/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3806763/5000000) (δ := 3709/500000000) (ψ := 188437/250000) 147 123
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t197 : ((-177303395647/2500000000000 : ℚ) : ℝ) ≤ stT147 197 := by
  have hc : ((-248857/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177303395647/2500000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-248857/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c198 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-398609/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3116837/5000000) (δ := 1873/250000000) (ψ := 188437/250000) 147 124
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t198 : ((-14164861239/250000000000 : ℚ) : ℝ) ≤ stT147 198 := by
  have hc : ((-199317/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14164861239/250000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-199317/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c199 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-22639/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4382283/10000000) (δ := 7411/1000000000) (ψ := 188437/250000) 147 124
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t199 : ((-32105620221/2500000000000 : ℚ) : ℝ) ≤ stT147 199 := by
  have hc : ((-90581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32105620221/2500000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-90581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c200 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((263353/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2540189/10000000) (δ := 231/31250000) (ψ := 188437/250000) 147 124
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t200 : ((2909387637/78125000000 : ℚ) : ℝ) ≤ stT147 200 := by
  have hc : ((8229/15625 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2909387637/78125000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((8229/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c201 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((3841/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -353623/5000000) (δ := 231/31250000) (ψ := 188437/250000) 147 124
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t201 : ((677272269/10000000000 : ℚ) : ℝ) ≤ stT147 201 := by
  have hc : ((4801/5000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((677272269/10000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((4801/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c202 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((901913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 558273/5000000) (δ := 7411/1000000000) (ψ := 188437/250000) 147 124
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t202 : ((634548101211/10000000000000 : ℚ) : ℝ) ≤ stT147 202 := by
  have hc : ((901863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((634548101211/10000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((901863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c203 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((96951/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2931371/10000000) (δ := 7511/1000000000) (ψ := 188437/250000) 147 124
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t203 : ((68037449487/2500000000000 : ℚ) : ℝ) ≤ stT147 203 := by
  have hc : ((193877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68037449487/2500000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((193877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c204 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-63693/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2368633/5000000) (δ := 7511/1000000000) (ψ := 188437/250000) 147 124
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t204 : ((-44601082123/2000000000000 : ℚ) : ℝ) ≤ stT147 204 := by
  have hc : ((-63703/200000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44601082123/2000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-63703/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c205 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-863889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6534341/10000000) (δ := 7511/1000000000) (ψ := 188437/250000) 147 124
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t205 : ((-603401779709/10000000000000 : ℚ) : ℝ) ≤ stT147 205 := by
  have hc : ((-863939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-603401779709/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-863939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c206 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-491239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7385293/10000000) (δ := 7499/1000000000) (ψ := 188437/250000) 147 125
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t206 : ((-668516273/9765625000 : ℚ) : ℝ) ≤ stT147 206 := by
  have hc : ((-15352/15625 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-668516273/9765625000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-15352/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c207 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-622129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2802819/5000000) (δ := 1851/250000000) (ψ := 188437/250000) 147 125
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t207 : ((-432444891771/10000000000000 : ℚ) : ℝ) ≤ stT147 207 := by
  have hc : ((-622179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-432444891771/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-622179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c208 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((3697/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -766909/2000000) (δ := 7399/1000000000) (ψ := 188437/250000) 147 125
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t208 : ((5119881/2000000000 : ℚ) : ℝ) ≤ stT147 208 := by
  have hc : ((923/25000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5119881/2000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((923/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c209 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((337889/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1035971/5000000) (δ := 469/62500000) (ψ := 188437/250000) 147 125
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t209 : ((14606578681/312500000000 : ℚ) : ℝ) ≤ stT147 209 := by
  have hc : ((42233/62500 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14606578681/312500000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((42233/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c210 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((991933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -158877/5000000) (δ := 1851/250000000) (ψ := 188437/250000) 147 125
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t210 : ((136892748479/2000000000000 : ℚ) : ℝ) ≤ stT147 210 := by
  have hc : ((991883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136892748479/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((991883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c211 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((841233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 357023/2500000) (δ := 7499/1000000000) (ψ := 188437/250000) 147 125
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t211 : ((144773482581/2500000000000 : ℚ) : ℝ) ≤ stT147 211 := by
  have hc : ((841183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144773482581/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((841183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c212 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((74961/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 791417/2500000) (δ := 469/62500000) (ψ := 188437/250000) 147 125
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t212 : ((51474779697/2500000000000 : ℚ) : ℝ) ≤ stT147 212 := by
  have hc : ((149897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51474779697/2500000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((149897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c213 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-377633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4895087/10000000) (δ := 7499/1000000000) (ψ := 188437/250000) 147 125
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t213 : ((-258784237087/10000000000000 : ℚ) : ℝ) ≤ stT147 213 := by
  have hc : ((-377683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258784237087/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-377683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c214 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-879957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 330821/500000) (δ := 7399/1000000000) (ψ := 188437/250000) 147 125
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t214 : ((-300780232551/5000000000000 : ℚ) : ℝ) ≤ stT147 214 := by
  have hc : ((-880007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-300780232551/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-880007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c215 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-19639/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3689129/5000000) (δ := 3753/500000000) (ψ := 188437/250000) 147 126
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t215 : ((-66971909/1000000000 : ℚ) : ℝ) ≤ stT147 215 := by
  have hc : ((-491/500 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66971909/1000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-491/500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c216 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-642969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5672911/10000000) (δ := 3753/500000000) (ψ := 188437/250000) 147 126
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t216 : ((-218759564933/5000000000000 : ℚ) : ℝ) ≤ stT147 216 := by
  have hc : ((-643019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218759564933/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-643019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c217 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-19389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1987733/5000000) (δ := 7497/1000000000) (ψ := 188437/250000) 147 126
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t217 : ((-2639213591/2000000000000 : ℚ) : ℝ) ≤ stT147 217 := by
  have hc : ((-19439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2639213591/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-19439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c218 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((305163/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2285811/10000000) (δ := 7397/1000000000) (ψ := 188437/250000) 147 126
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t218 : ((20666539033/500000000000 : ℚ) : ℝ) ≤ stT147 218 := by
  have hc : ((152569/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20666539033/500000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((152569/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c219 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((121371/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -301937/5000000) (δ := 7497/1000000000) (ψ := 188437/250000) 147 126
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t219 : ((328042608283/5000000000000 : ℚ) : ℝ) ≤ stT147 219 := by
  have hc : ((485459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((328042608283/5000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((485459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c220 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((454867/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1070383/10000000) (δ := 3703/500000000) (ψ := 188437/250000) 147 126
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t220 : ((153327010779/2500000000000 : ℚ) : ℝ) ≤ stT147 220 := by
  have hc : ((227421/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153327010779/2500000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((227421/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c221 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((2291/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2737069/10000000) (δ := 3703/500000000) (ψ := 188437/250000) 147 126
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t221 : ((192615423/6250000000 : ℚ) : ℝ) ≤ stT147 221 := by
  have hc : ((9163/20000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192615423/6250000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((9163/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c222 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-186577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 549523/1250000) (δ := 7497/1000000000) (ψ := 188437/250000) 147 126
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t222 : ((-125256017439/10000000000000 : ℚ) : ℝ) ≤ stT147 222 := by
  have hc : ((-186627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125256017439/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-186627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c223 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-750193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1511969/2500000) (δ := 7497/1000000000) (ψ := 188437/250000) 147 126
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t223 : ((-10048004499/200000000000 : ℚ) : ℝ) ≤ stT147 223 := by
  have hc : ((-750243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10048004499/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-750243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c224 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-498953/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3846091/5000000) (δ := 3753/500000000) (ψ := 188437/250000) 147 126
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t224 : ((-83348536653/1250000000000 : ℚ) : ℝ) ≤ stT147 224 := by
  have hc : ((-249489/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83348536653/1250000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-249489/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c225 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-415449/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -637879/1000000) (δ := 749/100000000) (ψ := 188437/250000) 147 127
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t225 : ((-138491402579/2500000000000 : ℚ) : ℝ) ≤ stT147 225 := by
  have hc : ((-207737/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138491402579/2500000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-207737/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c226 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-161473/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4749093/10000000) (δ := 1489/100000000) (ψ := 188437/250000) 147 127
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t226 : ((-53713508059/2500000000000 : ℚ) : ℝ) ≤ stT147 226 := by
  have hc : ((-80749/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53713508059/2500000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-80749/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c227 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((314729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1563281/5000000) (δ := 749/100000000) (ψ := 188437/250000) 147 127
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t227 : ((208859689917/10000000000000 : ℚ) : ℝ) ≤ stT147 227 := by
  have hc : ((314679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208859689917/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((314679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c228 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((822803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1511179/10000000) (δ := 749/100000000) (ψ := 188437/250000) 147 127
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t228 : ((272440669149/5000000000000 : ℚ) : ℝ) ≤ stT147 228 := by
  have hc : ((822753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272440669149/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((822753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c229 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((199849/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24287/2500000) (δ := 749/100000000) (ψ := 188437/250000) 147 127
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t229 : ((66028604151/1000000000000 : ℚ) : ℝ) ≤ stT147 229 := by
  have hc : ((199839/200000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66028604151/1000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((199839/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c230 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((777961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 212307/1250000) (δ := 739/100000000) (ψ := 188437/250000) 147 127
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t230 : ((25646947759/500000000000 : ℚ) : ℝ) ≤ stT147 230 := by
  have hc : ((777911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25646947759/500000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((777911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c231 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((250957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1646409/5000000) (δ := 739/100000000) (ψ := 188437/250000) 147 127
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t231 : ((165084511557/10000000000000 : ℚ) : ℝ) ≤ stT147 231 := by
  have hc : ((250907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165084511557/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((250907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c232 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-372139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4880271/10000000) (δ := 739/100000000) (ψ := 188437/250000) 147 127
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t232 : ((-244354360737/10000000000000 : ℚ) : ℝ) ≤ stT147 232 := by
  have hc : ((-372189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244354360737/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-372189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c233 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-848727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 258437/400000) (δ := 749/100000000) (ψ := 188437/250000) 147 127
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t233 : ((-278026242897/5000000000000 : ℚ) : ℝ) ≤ stT147 233 := by
  have hc : ((-848777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278026242897/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-848777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c234 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-199477/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3836573/5000000) (δ := 7483/1000000000) (ψ := 188437/250000) 147 128
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t234 : ((-130408841127/2000000000000 : ℚ) : ℝ) ≤ stT147 234 := by
  have hc : ((-199487/200000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130408841127/2000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-199487/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c235 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-765357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6105979/10000000) (δ := 7483/1000000000) (ψ := 188437/250000) 147 128
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t235 : ((-499297182903/10000000000000 : ℚ) : ℝ) ≤ stT147 235 := by
  have hc : ((-765407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-499297182903/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-765407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c236 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-244873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4545463/10000000) (δ := 47/6250000) (ψ := 188437/250000) 147 128
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t236 : ((-31886280447/2000000000000 : ℚ) : ℝ) ≤ stT147 236 := by
  have hc : ((-244923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31886280447/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-244923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c237 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((365501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2991563/10000000) (δ := 371/50000000) (ψ := 188437/250000) 147 128
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t237 : ((237385640619/10000000000000 : ℚ) : ℝ) ≤ stT147 237 := by
  have hc : ((365451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237385640619/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((365451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c238 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((837731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -361051/2500000) (δ := 47/6250000) (ψ := 188437/250000) 147 128
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t238 : ((542987337243/10000000000000 : ℚ) : ℝ) ≤ stT147 238 := by
  have hc : ((837681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((542987337243/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((837681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c239 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((249813/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 48343/5000000) (δ := 7483/1000000000) (ψ := 188437/250000) 147 128
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t239 : ((161582454223/2500000000000 : ℚ) : ℝ) ≤ stT147 239 := by
  have hc : ((499601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161582454223/2500000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((499601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c240 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((397297/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 815573/5000000) (δ := 371/50000000) (ψ := 188437/250000) 147 128
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t240 : ((32054735523/625000000000 : ℚ) : ℝ) ≤ stT147 240 := by
  have hc : ((49659/62500 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32054735523/625000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((49659/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c241 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((302307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3159211/10000000) (δ := 371/50000000) (ψ := 188437/250000) 147 128
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t241 : ((48675165023/2500000000000 : ℚ) : ℝ) ≤ stT147 241 := by
  have hc : ((302257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48675165023/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((302257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c242 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-59407/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 936191/2000000) (δ := 371/50000000) (ψ := 188437/250000) 147 128
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t242 : ((-1527789321/80000000000 : ℚ) : ℝ) ≤ stT147 242 := by
  have hc : ((-59417/200000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1527789321/80000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-59417/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c243 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-788133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1239283/2000000) (δ := 47/6250000) (ψ := 188437/250000) 147 128
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t243 : ((-505620182683/10000000000000 : ℚ) : ℝ) ≤ stT147 243 := by
  have hc : ((-788183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-505620182683/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-788183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c244 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-998241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 120401/156250) (δ := 47/6250000) (ψ := 188437/250000) 147 128
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t244 : ((-127818184767/2000000000000 : ℚ) : ℝ) ≤ stT147 244 := by
  have hc : ((-998291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127818184767/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-998291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c245 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-856733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6499243/10000000) (δ := 1841/125000000) (ψ := 188437/250000) 147 129
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t245 : ((-547378952691/10000000000000 : ℚ) : ℝ) ≤ stT147 245 := by
  have hc : ((-856783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-547378952691/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-856783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c246 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((-208489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5002287/10000000) (δ := 59/8000000) (ψ := 188437/250000) 147 129
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t246 : ((-66471865289/2500000000000 : ℚ) : ℝ) ≤ stT147 246 := by
  have hc : ((-104257/250000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66471865289/2500000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-104257/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c247 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((165467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3511413/10000000) (δ := 59/8000000) (ψ := 188437/250000) 147 129
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t247 : ((26313047607/2500000000000 : ℚ) : ℝ) ≤ stT147 247 := by
  have hc : ((165417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26313047607/2500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((165417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c248 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((137809/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1013283/5000000) (δ := 59/8000000) (ψ := 188437/250000) 147 129
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t248 : ((17500473/400000000 : ℚ) : ℝ) ≤ stT147 248 := by
  have hc : ((137799/200000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17500473/400000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((137799/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c249 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((976097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -547709/10000000) (δ := 1857/250000000) (ψ := 188437/250000) 147 129
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t249 : ((154636102257/2500000000000 : ℚ) : ℝ) ≤ stT147 249 := by
  have hc : ((976047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154636102257/2500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((976047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_c250 :
    |Real.cos (((147 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((932289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 231317/2500000) (δ := 941/125000000) (ψ := 188437/250000) 147 129
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st147_t250 : ((117919843349/2000000000000 : ℚ) : ℝ) ≤ stT147 250 := by
  have hc : ((932239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((147 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((188437/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st147_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117919843349/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((932239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st147_p1 : ((729079/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT147 (i+1) := by
  rw [Finset.sum_range_one]
  exact st147_t1

theorem st147_p2 : ((13094644011863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT147 (i+1))
      = (∑ i ∈ Finset.range 1, stT147 (i+1)) + stT147 2 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 1
    simpa using h
  have hprev := st147_p1
  have hstep := st147_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p3 : ((8086949996789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT147 (i+1))
      = (∑ i ∈ Finset.range 2, stT147 (i+1)) + stT147 3 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 2
    simpa using h
  have hprev := st147_p2
  have hstep := st147_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p4 : ((6145159608431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT147 (i+1))
      = (∑ i ∈ Finset.range 3, stT147 (i+1)) + stT147 4 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 3
    simpa using h
  have hprev := st147_p3
  have hstep := st147_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p5 : ((354996767419/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT147 (i+1))
      = (∑ i ∈ Finset.range 4, stT147 (i+1)) + stT147 5 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 4
    simpa using h
  have hprev := st147_p4
  have hstep := st147_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p6 : ((3027579129299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT147 (i+1))
      = (∑ i ∈ Finset.range 5, stT147 (i+1)) + stT147 6 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 5
    simpa using h
  have hprev := st147_p5
  have hstep := st147_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p7 : ((-56753093443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT147 (i+1))
      = (∑ i ∈ Finset.range 6, stT147 (i+1)) + stT147 7 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 6
    simpa using h
  have hprev := st147_p6
  have hstep := st147_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p8 : ((-358581069683/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT147 (i+1))
      = (∑ i ∈ Finset.range 7, stT147 (i+1)) + stT147 8 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 7
    simpa using h
  have hprev := st147_p7
  have hstep := st147_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p9 : ((-432971084561/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT147 (i+1))
      = (∑ i ∈ Finset.range 8, stT147 (i+1)) + stT147 9 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 8
    simpa using h
  have hprev := st147_p8
  have hstep := st147_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p10 : ((-134809951071/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT147 (i+1))
      = (∑ i ∈ Finset.range 9, stT147 (i+1)) + stT147 10 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 9
    simpa using h
  have hprev := st147_p9
  have hstep := st147_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p11 : ((-1321192648297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT147 (i+1))
      = (∑ i ∈ Finset.range 10, stT147 (i+1)) + stT147 11 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 10
    simpa using h
  have hprev := st147_p10
  have hstep := st147_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p12 : ((775090314563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT147 (i+1))
      = (∑ i ∈ Finset.range 11, stT147 (i+1)) + stT147 12 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 11
    simpa using h
  have hprev := st147_p11
  have hstep := st147_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p13 : ((1838063311313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT147 (i+1))
      = (∑ i ∈ Finset.range 12, stT147 (i+1)) + stT147 13 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 12
    simpa using h
  have hprev := st147_p12
  have hstep := st147_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p14 : ((880311061859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT147 (i+1))
      = (∑ i ∈ Finset.range 13, stT147 (i+1)) + stT147 14 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 13
    simpa using h
  have hprev := st147_p13
  have hstep := st147_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p15 : ((985773652713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT147 (i+1))
      = (∑ i ∈ Finset.range 14, stT147 (i+1)) + stT147 15 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 14
    simpa using h
  have hprev := st147_p14
  have hstep := st147_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p16 : ((1922799785927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT147 (i+1))
      = (∑ i ∈ Finset.range 15, stT147 (i+1)) + stT147 16 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 15
    simpa using h
  have hprev := st147_p15
  have hstep := st147_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p17 : ((630764150671/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT147 (i+1))
      = (∑ i ∈ Finset.range 16, stT147 (i+1)) + stT147 17 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 16
    simpa using h
  have hprev := st147_p16
  have hstep := st147_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p18 : ((796976887103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT147 (i+1))
      = (∑ i ∈ Finset.range 17, stT147 (i+1)) + stT147 18 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 17
    simpa using h
  have hprev := st147_p17
  have hstep := st147_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p19 : ((1048228373429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT147 (i+1))
      = (∑ i ∈ Finset.range 18, stT147 (i+1)) + stT147 19 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 18
    simpa using h
  have hprev := st147_p18
  have hstep := st147_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p20 : ((647556141539/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT147 (i+1))
      = (∑ i ∈ Finset.range 19, stT147 (i+1)) + stT147 20 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 19
    simpa using h
  have hprev := st147_p19
  have hstep := st147_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p21 : ((39421885817/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT147 (i+1))
      = (∑ i ∈ Finset.range 20, stT147 (i+1)) + stT147 21 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 20
    simpa using h
  have hprev := st147_p20
  have hstep := st147_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p22 : ((5619793727353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT147 (i+1))
      = (∑ i ∈ Finset.range 21, stT147 (i+1)) + stT147 22 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 21
    simpa using h
  have hprev := st147_p21
  have hstep := st147_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p23 : ((5785112284249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT147 (i+1))
      = (∑ i ∈ Finset.range 22, stT147 (i+1)) + stT147 23 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 22
    simpa using h
  have hprev := st147_p22
  have hstep := st147_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p24 : ((300083479159/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT147 (i+1))
      = (∑ i ∈ Finset.range 23, stT147 (i+1)) + stT147 24 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 23
    simpa using h
  have hprev := st147_p23
  have hstep := st147_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p25 : ((337976379159/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT147 (i+1))
      = (∑ i ∈ Finset.range 24, stT147 (i+1)) + stT147 25 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 24
    simpa using h
  have hprev := st147_p24
  have hstep := st147_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p26 : ((8303473153201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT147 (i+1))
      = (∑ i ∈ Finset.range 25, stT147 (i+1)) + stT147 26 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 25
    simpa using h
  have hprev := st147_p25
  have hstep := st147_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p27 : ((10223029112701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT147 (i+1))
      = (∑ i ∈ Finset.range 26, stT147 (i+1)) + stT147 27 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 26
    simpa using h
  have hprev := st147_p26
  have hstep := st147_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p28 : ((11231043159103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT147 (i+1))
      = (∑ i ∈ Finset.range 27, stT147 (i+1)) + stT147 28 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 27
    simpa using h
  have hprev := st147_p27
  have hstep := st147_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p29 : ((10241258822793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT147 (i+1))
      = (∑ i ∈ Finset.range 28, stT147 (i+1)) + stT147 29 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 28
    simpa using h
  have hprev := st147_p28
  have hstep := st147_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p30 : ((8492168774921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT147 (i+1))
      = (∑ i ∈ Finset.range 29, stT147 (i+1)) + stT147 30 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 29
    simpa using h
  have hprev := st147_p29
  have hstep := st147_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p31 : ((4409676976939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT147 (i+1))
      = (∑ i ∈ Finset.range 30, stT147 (i+1)) + stT147 31 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 30
    simpa using h
  have hprev := st147_p30
  have hstep := st147_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p32 : ((2635263434921/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT147 (i+1))
      = (∑ i ∈ Finset.range 31, stT147 (i+1)) + stT147 32 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 31
    simpa using h
  have hprev := st147_p31
  have hstep := st147_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p33 : ((2458766054891/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT147 (i+1))
      = (∑ i ∈ Finset.range 32, stT147 (i+1)) + stT147 33 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 32
    simpa using h
  have hprev := st147_p32
  have hstep := st147_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p34 : ((4285145599663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT147 (i+1))
      = (∑ i ∈ Finset.range 33, stT147 (i+1)) + stT147 34 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 33
    simpa using h
  have hprev := st147_p33
  have hstep := st147_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p35 : ((5070582708331/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT147 (i+1))
      = (∑ i ∈ Finset.range 34, stT147 (i+1)) + stT147 35 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 34
    simpa using h
  have hprev := st147_p34
  have hstep := st147_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p36 : ((1964206070527/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT147 (i+1))
      = (∑ i ∈ Finset.range 35, stT147 (i+1)) + stT147 36 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 35
    simpa using h
  have hprev := st147_p35
  have hstep := st147_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p37 : ((1754181087259/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT147 (i+1))
      = (∑ i ∈ Finset.range 36, stT147 (i+1)) + stT147 37 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 36
    simpa using h
  have hprev := st147_p36
  have hstep := st147_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p38 : ((415401632423/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT147 (i+1))
      = (∑ i ∈ Finset.range 37, stT147 (i+1)) + stT147 38 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 37
    simpa using h
  have hprev := st147_p37
  have hstep := st147_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p39 : ((9043333027903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT147 (i+1))
      = (∑ i ∈ Finset.range 38, stT147 (i+1)) + stT147 39 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 38
    simpa using h
  have hprev := st147_p38
  have hstep := st147_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p40 : ((9678148866937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT147 (i+1))
      = (∑ i ∈ Finset.range 39, stT147 (i+1)) + stT147 40 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 39
    simpa using h
  have hprev := st147_p39
  have hstep := st147_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p41 : ((9795119844763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT147 (i+1))
      = (∑ i ∈ Finset.range 40, stT147 (i+1)) + stT147 41 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 40
    simpa using h
  have hprev := st147_p40
  have hstep := st147_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p42 : ((9088294545213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT147 (i+1))
      = (∑ i ∈ Finset.range 41, stT147 (i+1)) + stT147 42 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 41
    simpa using h
  have hprev := st147_p41
  have hstep := st147_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p43 : ((10174886007323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT147 (i+1))
      = (∑ i ∈ Finset.range 42, stT147 (i+1)) + stT147 43 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 42
    simpa using h
  have hprev := st147_p42
  have hstep := st147_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p44 : ((4440793765417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT147 (i+1))
      = (∑ i ∈ Finset.range 43, stT147 (i+1)) + stT147 44 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 43
    simpa using h
  have hprev := st147_p43
  have hstep := st147_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p45 : ((20534126557/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT147 (i+1))
      = (∑ i ∈ Finset.range 44, stT147 (i+1)) + stT147 45 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 44
    simpa using h
  have hprev := st147_p44
  have hstep := st147_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p46 : ((442676398899/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT147 (i+1))
      = (∑ i ∈ Finset.range 45, stT147 (i+1)) + stT147 46 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 45
    simpa using h
  have hprev := st147_p45
  have hstep := st147_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p47 : ((10259754591569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT147 (i+1))
      = (∑ i ∈ Finset.range 46, stT147 (i+1)) + stT147 47 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 46
    simpa using h
  have hprev := st147_p46
  have hstep := st147_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p48 : ((8887532698241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT147 (i+1))
      = (∑ i ∈ Finset.range 47, stT147 (i+1)) + stT147 48 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 47
    simpa using h
  have hprev := st147_p47
  have hstep := st147_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p49 : ((10188335165143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT147 (i+1))
      = (∑ i ∈ Finset.range 48, stT147 (i+1)) + stT147 49 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 48
    simpa using h
  have hprev := st147_p48
  have hstep := st147_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p50 : ((1803864366221/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT147 (i+1))
      = (∑ i ∈ Finset.range 49, stT147 (i+1)) + stT147 50 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 49
    simpa using h
  have hprev := st147_p49
  have hstep := st147_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p51 : ((1993178581493/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT147 (i+1))
      = (∑ i ∈ Finset.range 50, stT147 (i+1)) + stT147 51 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 50
    simpa using h
  have hprev := st147_p50
  have hstep := st147_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p52 : ((1169512631311/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT147 (i+1))
      = (∑ i ∈ Finset.range 51, stT147 (i+1)) + stT147 52 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 51
    simpa using h
  have hprev := st147_p51
  have hstep := st147_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p53 : ((9511918680873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT147 (i+1))
      = (∑ i ∈ Finset.range 52, stT147 (i+1)) + stT147 53 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 52
    simpa using h
  have hprev := st147_p52
  have hstep := st147_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p54 : ((9888083923521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT147 (i+1))
      = (∑ i ∈ Finset.range 53, stT147 (i+1)) + stT147 54 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 53
    simpa using h
  have hprev := st147_p53
  have hstep := st147_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p55 : ((8994453397921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT147 (i+1))
      = (∑ i ∈ Finset.range 54, stT147 (i+1)) + stT147 55 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 54
    simpa using h
  have hprev := st147_p54
  have hstep := st147_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p56 : ((10248052746969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT147 (i+1))
      = (∑ i ∈ Finset.range 55, stT147 (i+1)) + stT147 56 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 55
    simpa using h
  have hprev := st147_p55
  have hstep := st147_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p57 : ((8946354695889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT147 (i+1))
      = (∑ i ∈ Finset.range 56, stT147 (i+1)) + stT147 57 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 56
    simpa using h
  have hprev := st147_p56
  have hstep := st147_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p58 : ((9887832088401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT147 (i+1))
      = (∑ i ∈ Finset.range 57, stT147 (i+1)) + stT147 58 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 57
    simpa using h
  have hprev := st147_p57
  have hstep := st147_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p59 : ((9666411844761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT147 (i+1))
      = (∑ i ∈ Finset.range 58, stT147 (i+1)) + stT147 59 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 58
    simpa using h
  have hprev := st147_p58
  have hstep := st147_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p60 : ((4523653077773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT147 (i+1))
      = (∑ i ∈ Finset.range 59, stT147 (i+1)) + stT147 60 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 59
    simpa using h
  have hprev := st147_p59
  have hstep := st147_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p61 : ((5123010623541/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT147 (i+1))
      = (∑ i ∈ Finset.range 60, stT147 (i+1)) + stT147 61 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 60
    simpa using h
  have hprev := st147_p60
  have hstep := st147_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p62 : ((453623731449/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT147 (i+1))
      = (∑ i ∈ Finset.range 61, stT147 (i+1)) + stT147 62 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 61
    simpa using h
  have hprev := st147_p61
  have hstep := st147_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p63 : ((2387525138901/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT147 (i+1))
      = (∑ i ∈ Finset.range 62, stT147 (i+1)) + stT147 63 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 62
    simpa using h
  have hprev := st147_p62
  have hstep := st147_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p64 : ((2519967951401/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT147 (i+1))
      = (∑ i ∈ Finset.range 63, stT147 (i+1)) + stT147 64 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 63
    simpa using h
  have hprev := st147_p63
  have hstep := st147_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p65 : ((444230026631/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT147 (i+1))
      = (∑ i ∈ Finset.range 64, stT147 (i+1)) + stT147 65 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 64
    simpa using h
  have hprev := st147_p64
  have hstep := st147_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p66 : ((4940784124347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT147 (i+1))
      = (∑ i ∈ Finset.range 65, stT147 (i+1)) + stT147 66 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 65
    simpa using h
  have hprev := st147_p65
  have hstep := st147_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p67 : ((9865484634019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT147 (i+1))
      = (∑ i ∈ Finset.range 66, stT147 (i+1)) + stT147 67 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 66
    simpa using h
  have hprev := st147_p66
  have hstep := st147_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p68 : ((8878548255227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT147 (i+1))
      = (∑ i ∈ Finset.range 67, stT147 (i+1)) + stT147 68 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 67
    simpa using h
  have hprev := st147_p67
  have hstep := st147_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p69 : ((9998497352627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT147 (i+1))
      = (∑ i ∈ Finset.range 68, stT147 (i+1)) + stT147 69 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 68
    simpa using h
  have hprev := st147_p68
  have hstep := st147_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p70 : ((9797507643987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT147 (i+1))
      = (∑ i ∈ Finset.range 69, stT147 (i+1)) + stT147 70 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 69
    simpa using h
  have hprev := st147_p69
  have hstep := st147_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p71 : ((8877070381119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT147 (i+1))
      = (∑ i ∈ Finset.range 70, stT147 (i+1)) + stT147 71 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 70
    simpa using h
  have hprev := st147_p70
  have hstep := st147_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p72 : ((498070387281/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT147 (i+1))
      = (∑ i ∈ Finset.range 71, stT147 (i+1)) + stT147 72 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 71
    simpa using h
  have hprev := st147_p71
  have hstep := st147_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p73 : ((309301109593/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT147 (i+1))
      = (∑ i ∈ Finset.range 72, stT147 (i+1)) + stT147 73 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 72
    simpa using h
  have hprev := st147_p72
  have hstep := st147_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p74 : ((4434227547329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT147 (i+1))
      = (∑ i ∈ Finset.range 73, stT147 (i+1)) + stT147 74 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 73
    simpa using h
  have hprev := st147_p73
  have hstep := st147_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p75 : ((4881416876579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT147 (i+1))
      = (∑ i ∈ Finset.range 74, stT147 (i+1)) + stT147 75 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 74
    simpa using h
  have hprev := st147_p74
  have hstep := st147_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p76 : ((5055508904639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT147 (i+1))
      = (∑ i ∈ Finset.range 75, stT147 (i+1)) + stT147 76 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 75
    simpa using h
  have hprev := st147_p75
  have hstep := st147_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p77 : ((4486187957977/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT147 (i+1))
      = (∑ i ∈ Finset.range 76, stT147 (i+1)) + stT147 77 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 76
    simpa using h
  have hprev := st147_p76
  have hstep := st147_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p78 : ((9380023942879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT147 (i+1))
      = (∑ i ∈ Finset.range 77, stT147 (i+1)) + stT147 78 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 77
    simpa using h
  have hprev := st147_p77
  have hstep := st147_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p79 : ((5130853123019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT147 (i+1))
      = (∑ i ∈ Finset.range 78, stT147 (i+1)) + stT147 79 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 78
    simpa using h
  have hprev := st147_p78
  have hstep := st147_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p80 : ((4676609325227/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT147 (i+1))
      = (∑ i ∈ Finset.range 79, stT147 (i+1)) + stT147 80 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 79
    simpa using h
  have hprev := st147_p79
  have hstep := st147_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p81 : ((4477231943503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT147 (i+1))
      = (∑ i ∈ Finset.range 80, stT147 (i+1)) + stT147 81 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 80
    simpa using h
  have hprev := st147_p80
  have hstep := st147_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p82 : ((10048808026871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT147 (i+1))
      = (∑ i ∈ Finset.range 81, stT147 (i+1)) + stT147 82 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 81
    simpa using h
  have hprev := st147_p81
  have hstep := st147_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p83 : ((4982189212477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT147 (i+1))
      = (∑ i ∈ Finset.range 82, stT147 (i+1)) + stT147 83 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 82
    simpa using h
  have hprev := st147_p82
  have hstep := st147_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p84 : ((2227947974991/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT147 (i+1))
      = (∑ i ∈ Finset.range 83, stT147 (i+1)) + stT147 84 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 83
    simpa using h
  have hprev := st147_p83
  have hstep := st147_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p85 : ((117116538257/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT147 (i+1))
      = (∑ i ∈ Finset.range 84, stT147 (i+1)) + stT147 85 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 84
    simpa using h
  have hprev := st147_p84
  have hstep := st147_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p86 : ((256721586099/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT147 (i+1))
      = (∑ i ∈ Finset.range 85, stT147 (i+1)) + stT147 86 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 85
    simpa using h
  have hprev := st147_p85
  have hstep := st147_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p87 : ((1913558534313/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT147 (i+1))
      = (∑ i ∈ Finset.range 86, stT147 (i+1)) + stT147 87 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 86
    simpa using h
  have hprev := st147_p86
  have hstep := st147_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p88 : ((8841974000053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT147 (i+1))
      = (∑ i ∈ Finset.range 87, stT147 (i+1)) + stT147 88 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 87
    simpa using h
  have hprev := st147_p87
  have hstep := st147_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p89 : ((9680179347767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT147 (i+1))
      = (∑ i ∈ Finset.range 88, stT147 (i+1)) + stT147 89 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 88
    simpa using h
  have hprev := st147_p88
  have hstep := st147_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p90 : ((10263937605551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT147 (i+1))
      = (∑ i ∈ Finset.range 89, stT147 (i+1)) + stT147 90 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 89
    simpa using h
  have hprev := st147_p89
  have hstep := st147_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p91 : ((1170156506757/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT147 (i+1))
      = (∑ i ∈ Finset.range 90, stT147 (i+1)) + stT147 91 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 90
    simpa using h
  have hprev := st147_p90
  have hstep := st147_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p92 : ((2215872542807/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT147 (i+1))
      = (∑ i ∈ Finset.range 91, stT147 (i+1)) + stT147 92 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 91
    simpa using h
  have hprev := st147_p91
  have hstep := st147_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p93 : ((9783557091459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT147 (i+1))
      = (∑ i ∈ Finset.range 92, stT147 (i+1)) + stT147 93 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 92
    simpa using h
  have hprev := st147_p92
  have hstep := st147_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p94 : ((2564458594617/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT147 (i+1))
      = (∑ i ∈ Finset.range 93, stT147 (i+1)) + stT147 94 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 93
    simpa using h
  have hprev := st147_p93
  have hstep := st147_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p95 : ((4677011400957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT147 (i+1))
      = (∑ i ∈ Finset.range 94, stT147 (i+1)) + stT147 95 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 94
    simpa using h
  have hprev := st147_p94
  have hstep := st147_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p96 : ((2210693842959/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT147 (i+1))
      = (∑ i ∈ Finset.range 95, stT147 (i+1)) + stT147 96 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 95
    simpa using h
  have hprev := st147_p95
  have hstep := st147_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p97 : ((48482056379/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT147 (i+1))
      = (∑ i ∈ Finset.range 96, stT147 (i+1)) + stT147 97 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 96
    simpa using h
  have hprev := st147_p96
  have hstep := st147_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p98 : ((1286960998801/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT147 (i+1))
      = (∑ i ∈ Finset.range 97, stT147 (i+1)) + stT147 98 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 97
    simpa using h
  have hprev := st147_p97
  have hstep := st147_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p99 : ((4767892896937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT147 (i+1))
      = (∑ i ∈ Finset.range 98, stT147 (i+1)) + stT147 99 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 98
    simpa using h
  have hprev := st147_p98
  have hstep := st147_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p100 : ((4406776396937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT147 (i+1))
      = (∑ i ∈ Finset.range 99, stT147 (i+1)) + stT147 100 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 99
    simpa using h
  have hprev := st147_p99
  have hstep := st147_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p101 : ((9420235808107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT147 (i+1))
      = (∑ i ∈ Finset.range 100, stT147 (i+1)) + stT147 101 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 100
    simpa using h
  have hprev := st147_p100
  have hstep := st147_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p102 : ((642053892589/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT147 (i+1))
      = (∑ i ∈ Finset.range 101, stT147 (i+1)) + stT147 102 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 101
    simpa using h
  have hprev := st147_p101
  have hstep := st147_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p103 : ((4946098393267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT147 (i+1))
      = (∑ i ∈ Finset.range 102, stT147 (i+1)) + stT147 103 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 102
    simpa using h
  have hprev := st147_p102
  have hstep := st147_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p104 : ((4470555831507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT147 (i+1))
      = (∑ i ∈ Finset.range 103, stT147 (i+1)) + stT147 104 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 103
    simpa using h
  have hprev := st147_p103
  have hstep := st147_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p105 : ((4510508689557/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT147 (i+1))
      = (∑ i ∈ Finset.range 104, stT147 (i+1)) + stT147 105 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 104
    simpa using h
  have hprev := st147_p104
  have hstep := st147_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p106 : ((2496959102671/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT147 (i+1))
      = (∑ i ∈ Finset.range 105, stT147 (i+1)) + stT147 106 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 105
    simpa using h
  have hprev := st147_p105
  have hstep := st147_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p107 : ((2565107465203/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT147 (i+1))
      = (∑ i ∈ Finset.range 106, stT147 (i+1)) + stT147 107 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 106
    simpa using h
  have hprev := st147_p106
  have hstep := st147_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p108 : ((4705507168787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT147 (i+1))
      = (∑ i ∈ Finset.range 107, stT147 (i+1)) + stT147 108 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 107
    simpa using h
  have hprev := st147_p107
  have hstep := st147_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p109 : ((351604617463/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT147 (i+1))
      = (∑ i ∈ Finset.range 108, stT147 (i+1)) + stT147 109 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 108
    simpa using h
  have hprev := st147_p108
  have hstep := st147_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p110 : ((9357385281171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT147 (i+1))
      = (∑ i ∈ Finset.range 109, stT147 (i+1)) + stT147 110 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 109
    simpa using h
  have hprev := st147_p109
  have hstep := st147_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p111 : ((204654849539/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT147 (i+1))
      = (∑ i ∈ Finset.range 110, stT147 (i+1)) + stT147 111 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 110
    simpa using h
  have hprev := st147_p110
  have hstep := st147_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p112 : ((5048360252363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT147 (i+1))
      = (∑ i ∈ Finset.range 111, stT147 (i+1)) + stT147 112 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 111
    simpa using h
  have hprev := st147_p111
  have hstep := st147_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p113 : ((9162685208873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT147 (i+1))
      = (∑ i ∈ Finset.range 112, stT147 (i+1)) + stT147 113 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 112
    simpa using h
  have hprev := st147_p112
  have hstep := st147_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p114 : ((8801931013393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT147 (i+1))
      = (∑ i ∈ Finset.range 113, stT147 (i+1)) + stT147 114 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 113
    simpa using h
  have hprev := st147_p113
  have hstep := st147_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p115 : ((9525628717713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT147 (i+1))
      = (∑ i ∈ Finset.range 114, stT147 (i+1)) + stT147 115 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 114
    simpa using h
  have hprev := st147_p114
  have hstep := st147_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p116 : ((10296866378637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT147 (i+1))
      = (∑ i ∈ Finset.range 115, stT147 (i+1)) + stT147 116 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 115
    simpa using h
  have hprev := st147_p115
  have hstep := st147_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p117 : ((10040034453831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT147 (i+1))
      = (∑ i ∈ Finset.range 116, stT147 (i+1)) + stT147 117 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 116
    simpa using h
  have hprev := st147_p116
  have hstep := st147_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p118 : ((9120087285981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT147 (i+1))
      = (∑ i ∈ Finset.range 117, stT147 (i+1)) + stT147 118 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 117
    simpa using h
  have hprev := st147_p117
  have hstep := st147_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p119 : ((4394890692801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT147 (i+1))
      = (∑ i ∈ Finset.range 118, stT147 (i+1)) + stT147 119 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 118
    simpa using h
  have hprev := st147_p118
  have hstep := st147_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p120 : ((2370622034403/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT147 (i+1))
      = (∑ i ∈ Finset.range 119, stT147 (i+1)) + stT147 120 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 119
    simpa using h
  have hprev := st147_p119
  have hstep := st147_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p121 : ((2568882745233/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT147 (i+1))
      = (∑ i ∈ Finset.range 120, stT147 (i+1)) + stT147 121 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 120
    simpa using h
  have hprev := st147_p120
  have hstep := st147_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p122 : ((633773356659/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT147 (i+1))
      = (∑ i ∈ Finset.range 121, stT147 (i+1)) + stT147 122 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 121
    simpa using h
  have hprev := st147_p121
  have hstep := st147_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p123 : ((2315146809361/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT147 (i+1))
      = (∑ i ∈ Finset.range 122, stT147 (i+1)) + stT147 123 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 122
    simpa using h
  have hprev := st147_p122
  have hstep := st147_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p124 : ((8752364123253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT147 (i+1))
      = (∑ i ∈ Finset.range 123, stT147 (i+1)) + stT147 124 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 123
    simpa using h
  have hprev := st147_p123
  have hstep := st147_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p125 : ((9241910853163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT147 (i+1))
      = (∑ i ∈ Finset.range 124, stT147 (i+1)) + stT147 125 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 124
    simpa using h
  have hprev := st147_p124
  have hstep := st147_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p126 : ((10118381721353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT147 (i+1))
      = (∑ i ∈ Finset.range 125, stT147 (i+1)) + stT147 126 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 125
    simpa using h
  have hprev := st147_p125
  have hstep := st147_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p127 : ((2063952013341/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT147 (i+1))
      = (∑ i ∈ Finset.range 126, stT147 (i+1)) + stT147 127 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 126
    simpa using h
  have hprev := st147_p126
  have hstep := st147_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p128 : ((9614379976041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT147 (i+1))
      = (∑ i ∈ Finset.range 127, stT147 (i+1)) + stT147 128 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 127
    simpa using h
  have hprev := st147_p127
  have hstep := st147_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p129 : ((552529246831/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT147 (i+1))
      = (∑ i ∈ Finset.range 128, stT147 (i+1)) + stT147 129 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 128
    simpa using h
  have hprev := st147_p128
  have hstep := st147_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p130 : ((4447159216719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT147 (i+1))
      = (∑ i ∈ Finset.range 129, stT147 (i+1)) + stT147 130 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 129
    simpa using h
  have hprev := st147_p129
  have hstep := st147_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p131 : ((4852360852467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT147 (i+1))
      = (∑ i ∈ Finset.range 130, stT147 (i+1)) + stT147 131 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 130
    simpa using h
  have hprev := st147_p130
  have hstep := st147_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p132 : ((1035035115247/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT147 (i+1))
      = (∑ i ∈ Finset.range 131, stT147 (i+1)) + stT147 132 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 131
    simpa using h
  have hprev := st147_p131
  have hstep := st147_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p133 : ((505798435907/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT147 (i+1))
      = (∑ i ∈ Finset.range 132, stT147 (i+1)) + stT147 133 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 132
    simpa using h
  have hprev := st147_p132
  have hstep := st147_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p134 : ((231714990401/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT147 (i+1))
      = (∑ i ∈ Finset.range 133, stT147 (i+1)) + stT147 134 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 133
    simpa using h
  have hprev := st147_p133
  have hstep := st147_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p135 : ((2182871844739/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT147 (i+1))
      = (∑ i ∈ Finset.range 134, stT147 (i+1)) + stT147 135 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 134
    simpa using h
  have hprev := st147_p134
  have hstep := st147_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p136 : ((113425446383/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT147 (i+1))
      = (∑ i ∈ Finset.range 135, stT147 (i+1)) + stT147 136 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 135
    simpa using h
  have hprev := st147_p135
  have hstep := st147_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p137 : ((9925418693923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT147 (i+1))
      = (∑ i ∈ Finset.range 136, stT147 (i+1)) + stT147 137 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 136
    simpa using h
  have hprev := st147_p136
  have hstep := st147_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p138 : ((10395132390907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT147 (i+1))
      = (∑ i ∈ Finset.range 137, stT147 (i+1)) + stT147 138 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 137
    simpa using h
  have hprev := st147_p137
  have hstep := st147_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p139 : ((500290554767/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT147 (i+1))
      = (∑ i ∈ Finset.range 138, stT147 (i+1)) + stT147 139 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 138
    simpa using h
  have hprev := st147_p138
  have hstep := st147_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p140 : ((916129672283/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT147 (i+1))
      = (∑ i ∈ Finset.range 139, stT147 (i+1)) + stT147 140 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 139
    simpa using h
  have hprev := st147_p139
  have hstep := st147_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p141 : ((4355265748111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT147 (i+1))
      = (∑ i ∈ Finset.range 140, stT147 (i+1)) + stT147 141 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 140
    simpa using h
  have hprev := st147_p140
  have hstep := st147_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p142 : ((1136703671407/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT147 (i+1))
      = (∑ i ∈ Finset.range 141, stT147 (i+1)) + stT147 142 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 141
    simpa using h
  have hprev := st147_p141
  have hstep := st147_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p143 : ((4964029617421/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT147 (i+1))
      = (∑ i ∈ Finset.range 142, stT147 (i+1)) + stT147 143 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 142
    simpa using h
  have hprev := st147_p142
  have hstep := st147_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p144 : ((5203212855081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT147 (i+1))
      = (∑ i ∈ Finset.range 143, stT147 (i+1)) + stT147 144 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 143
    simpa using h
  have hprev := st147_p143
  have hstep := st147_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p145 : ((10078542975697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT147 (i+1))
      = (∑ i ∈ Finset.range 144, stT147 (i+1)) + stT147 145 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 144
    simpa using h
  have hprev := st147_p144
  have hstep := st147_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p146 : ((9260773900613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT147 (i+1))
      = (∑ i ∈ Finset.range 145, stT147 (i+1)) + stT147 146 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 145
    simpa using h
  have hprev := st147_p145
  have hstep := st147_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p147 : ((4357805981431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT147 (i+1))
      = (∑ i ∈ Finset.range 146, stT147 (i+1)) + stT147 147 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 146
    simpa using h
  have hprev := st147_p146
  have hstep := st147_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p148 : ((1117304864797/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT147 (i+1))
      = (∑ i ∈ Finset.range 147, stT147 (i+1)) + stT147 148 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 147
    simpa using h
  have hprev := st147_p147
  have hstep := st147_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p149 : ((9719494573007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT147 (i+1))
      = (∑ i ∈ Finset.range 148, stT147 (i+1)) + stT147 149 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 148
    simpa using h
  have hprev := st147_p148
  have hstep := st147_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p150 : ((10355900132767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT147 (i+1))
      = (∑ i ∈ Finset.range 149, stT147 (i+1)) + stT147 150 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 149
    simpa using h
  have hprev := st147_p149
  have hstep := st147_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p151 : ((2057692613183/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT147 (i+1))
      = (∑ i ∈ Finset.range 150, stT147 (i+1)) + stT147 151 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 150
    simpa using h
  have hprev := st147_p150
  have hstep := st147_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p152 : ((9583554247463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT147 (i+1))
      = (∑ i ∈ Finset.range 151, stT147 (i+1)) + stT147 152 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 151
    simpa using h
  have hprev := st147_p151
  have hstep := st147_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p153 : ((1770853639807/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT147 (i+1))
      = (∑ i ∈ Finset.range 152, stT147 (i+1)) + stT147 153 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 152
    simpa using h
  have hprev := st147_p152
  have hstep := st147_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p154 : ((8720456454947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT147 (i+1))
      = (∑ i ∈ Finset.range 153, stT147 (i+1)) + stT147 154 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 153
    simpa using h
  have hprev := st147_p153
  have hstep := st147_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p155 : ((9287969232959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT147 (i+1))
      = (∑ i ∈ Finset.range 154, stT147 (i+1)) + stT147 155 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 154
    simpa using h
  have hprev := st147_p154
  have hstep := st147_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p156 : ((10078441104959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT147 (i+1))
      = (∑ i ∈ Finset.range 155, stT147 (i+1)) + stT147 156 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 155
    simpa using h
  have hprev := st147_p155
  have hstep := st147_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p157 : ((10441458502919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT147 (i+1))
      = (∑ i ∈ Finset.range 156, stT147 (i+1)) + stT147 157 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 156
    simpa using h
  have hprev := st147_p156
  have hstep := st147_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p158 : ((10087475766377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT147 (i+1))
      = (∑ i ∈ Finset.range 157, stT147 (i+1)) + stT147 158 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 157
    simpa using h
  have hprev := st147_p157
  have hstep := st147_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p159 : ((9307522606261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT147 (i+1))
      = (∑ i ∈ Finset.range 158, stT147 (i+1)) + stT147 159 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 158
    simpa using h
  have hprev := st147_p158
  have hstep := st147_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p160 : ((8723325370771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT147 (i+1))
      = (∑ i ∈ Finset.range 159, stT147 (i+1)) + stT147 160 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 159
    simpa using h
  have hprev := st147_p159
  have hstep := st147_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p161 : ((8789752010231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT147 (i+1))
      = (∑ i ∈ Finset.range 160, stT147 (i+1)) + stT147 161 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 160
    simpa using h
  have hprev := st147_p160
  have hstep := st147_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p162 : ((9448558515407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT147 (i+1))
      = (∑ i ∈ Finset.range 161, stT147 (i+1)) + stT147 162 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 161
    simpa using h
  have hprev := st147_p161
  have hstep := st147_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p163 : ((10189899223467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT147 (i+1))
      = (∑ i ∈ Finset.range 162, stT147 (i+1)) + stT147 163 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 162
    simpa using h
  have hprev := st147_p162
  have hstep := st147_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p164 : ((10452644126371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT147 (i+1))
      = (∑ i ∈ Finset.range 163, stT147 (i+1)) + stT147 164 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 163
    simpa using h
  have hprev := st147_p163
  have hstep := st147_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p165 : ((10045437768437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT147 (i+1))
      = (∑ i ∈ Finset.range 164, stT147 (i+1)) + stT147 165 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 164
    simpa using h
  have hprev := st147_p164
  have hstep := st147_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p166 : ((4638009939181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT147 (i+1))
      = (∑ i ∈ Finset.range 165, stT147 (i+1)) + stT147 166 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 165
    simpa using h
  have hprev := st147_p165
  have hstep := st147_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p167 : ((4355077056973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT147 (i+1))
      = (∑ i ∈ Finset.range 166, stT147 (i+1)) + stT147 167 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 166
    simpa using h
  have hprev := st147_p166
  have hstep := st147_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p168 : ((4377231138913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT147 (i+1))
      = (∑ i ∈ Finset.range 167, stT147 (i+1)) + stT147 168 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 167
    simpa using h
  have hprev := st147_p167
  have hstep := st147_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p169 : ((2342755223009/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT147 (i+1))
      = (∑ i ∈ Finset.range 168, stT147 (i+1)) + stT147 169 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 168
    simpa using h
  have hprev := st147_p168
  have hstep := st147_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p170 : ((2529594172603/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT147 (i+1))
      = (∑ i ∈ Finset.range 169, stT147 (i+1)) + stT147 170 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 169
    simpa using h
  have hprev := st147_p169
  have hstep := st147_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p171 : ((5236493798389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT147 (i+1))
      = (∑ i ∈ Finset.range 170, stT147 (i+1)) + stT147 171 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 170
    simpa using h
  have hprev := st147_p170
  have hstep := st147_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p172 : ((5096869130201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT147 (i+1))
      = (∑ i ∈ Finset.range 171, stT147 (i+1)) + stT147 172 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 171
    simpa using h
  have hprev := st147_p171
  have hstep := st147_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p173 : ((4738942447407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT147 (i+1))
      = (∑ i ∈ Finset.range 172, stT147 (i+1)) + stT147 173 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 172
    simpa using h
  have hprev := st147_p172
  have hstep := st147_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p174 : ((4406922376971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT147 (i+1))
      = (∑ i ∈ Finset.range 173, stT147 (i+1)) + stT147 174 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 173
    simpa using h
  have hprev := st147_p173
  have hstep := st147_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p175 : ((4322636293471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT147 (i+1))
      = (∑ i ∈ Finset.range 174, stT147 (i+1)) + stT147 175 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 174
    simpa using h
  have hprev := st147_p174
  have hstep := st147_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p176 : ((2269689375129/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT147 (i+1))
      = (∑ i ∈ Finset.range 175, stT147 (i+1)) + stT147 176 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 175
    simpa using h
  have hprev := st147_p175
  have hstep := st147_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p177 : ((2456121635801/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT147 (i+1))
      = (∑ i ∈ Finset.range 176, stT147 (i+1)) + stT147 177 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 176
    simpa using h
  have hprev := st147_p176
  have hstep := st147_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p178 : ((10396265517023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT147 (i+1))
      = (∑ i ∈ Finset.range 177, stT147 (i+1)) + stT147 178 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 177
    simpa using h
  have hprev := st147_p177
  have hstep := st147_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p179 : ((10429288690193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT147 (i+1))
      = (∑ i ∈ Finset.range 178, stT147 (i+1)) + stT147 179 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 178
    simpa using h
  have hprev := st147_p178
  have hstep := st147_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p180 : ((9907878627173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT147 (i+1))
      = (∑ i ∈ Finset.range 179, stT147 (i+1)) + stT147 180 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 179
    simpa using h
  have hprev := st147_p179
  have hstep := st147_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p181 : ((9164671335983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT147 (i+1))
      = (∑ i ∈ Finset.range 180, stT147 (i+1)) + stT147 181 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 180
    simpa using h
  have hprev := st147_p180
  have hstep := st147_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p182 : ((8663406953483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT147 (i+1))
      = (∑ i ∈ Finset.range 181, stT147 (i+1)) + stT147 182 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 181
    simpa using h
  have hprev := st147_p181
  have hstep := st147_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p183 : ((2177459910539/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT147 (i+1))
      = (∑ i ∈ Finset.range 182, stT147 (i+1)) + stT147 183 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 182
    simpa using h
  have hprev := st147_p182
  have hstep := st147_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p184 : ((4635204471251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT147 (i+1))
      = (∑ i ∈ Finset.range 183, stT147 (i+1)) + stT147 184 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 183
    simpa using h
  have hprev := st147_p183
  have hstep := st147_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p185 : ((25006534279/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT147 (i+1))
      = (∑ i ∈ Finset.range 184, stT147 (i+1)) + stT147 185 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 184
    simpa using h
  have hprev := st147_p184
  have hstep := st147_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p186 : ((32713749309/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT147 (i+1))
      = (∑ i ∈ Finset.range 185, stT147 (i+1)) + stT147 186 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 185
    simpa using h
  have hprev := st147_p185
  have hstep := st147_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p187 : ((1299436116961/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT147 (i+1))
      = (∑ i ∈ Finset.range 186, stT147 (i+1)) + stT147 187 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 186
    simpa using h
  have hprev := st147_p186
  have hstep := st147_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p188 : ((4915782317569/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT147 (i+1))
      = (∑ i ∈ Finset.range 187, stT147 (i+1)) + stT147 188 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 187
    simpa using h
  have hprev := st147_p187
  have hstep := st147_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p189 : ((364290784077/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT147 (i+1))
      = (∑ i ∈ Finset.range 188, stT147 (i+1)) + stT147 189 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 188
    simpa using h
  have hprev := st147_p188
  have hstep := st147_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p190 : ((8638643380913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT147 (i+1))
      = (∑ i ∈ Finset.range 189, stT147 (i+1)) + stT147 190 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 189
    simpa using h
  have hprev := st147_p189
  have hstep := st147_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p191 : ((8688821067091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT147 (i+1))
      = (∑ i ∈ Finset.range 190, stT147 (i+1)) + stT147 191 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 190
    simpa using h
  have hprev := st147_p190
  have hstep := st147_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p192 : ((9224771814023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT147 (i+1))
      = (∑ i ∈ Finset.range 191, stT147 (i+1)) + stT147 192 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 191
    simpa using h
  have hprev := st147_p191
  have hstep := st147_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p193 : ((621514316623/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT147 (i+1))
      = (∑ i ∈ Finset.range 192, stT147 (i+1)) + stT147 193 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 192
    simpa using h
  have hprev := st147_p192
  have hstep := st147_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p194 : ((522486231343/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT147 (i+1))
      = (∑ i ∈ Finset.range 193, stT147 (i+1)) + stT147 194 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 193
    simpa using h
  have hprev := st147_p193
  have hstep := st147_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p195 : ((261696952919/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT147 (i+1))
      = (∑ i ∈ Finset.range 194, stT147 (i+1)) + stT147 195 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 194
    simpa using h
  have hprev := st147_p194
  have hstep := st147_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p196 : ((249834091031/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT147 (i+1))
      = (∑ i ∈ Finset.range 195, stT147 (i+1)) + stT147 196 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 195
    simpa using h
  have hprev := st147_p195
  have hstep := st147_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p197 : ((2321037514663/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT147 (i+1))
      = (∑ i ∈ Finset.range 196, stT147 (i+1)) + stT147 197 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 196
    simpa using h
  have hprev := st147_p196
  have hstep := st147_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p198 : ((2179388902273/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT147 (i+1))
      = (∑ i ∈ Finset.range 197, stT147 (i+1)) + stT147 198 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 197
    simpa using h
  have hprev := st147_p197
  have hstep := st147_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p199 : ((536820820513/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT147 (i+1))
      = (∑ i ∈ Finset.range 198, stT147 (i+1)) + stT147 199 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 198
    simpa using h
  have hprev := st147_p198
  have hstep := st147_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p200 : ((560095921609/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT147 (i+1))
      = (∑ i ∈ Finset.range 199, stT147 (i+1)) + stT147 200 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 199
    simpa using h
  have hprev := st147_p199
  have hstep := st147_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p201 : ((1204850876843/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT147 (i+1))
      = (∑ i ∈ Finset.range 200, stT147 (i+1)) + stT147 201 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 200
    simpa using h
  have hprev := st147_p200
  have hstep := st147_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p202 : ((2054671023191/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT147 (i+1))
      = (∑ i ∈ Finset.range 201, stT147 (i+1)) + stT147 202 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 201
    simpa using h
  have hprev := st147_p201
  have hstep := st147_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p203 : ((10545504913903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT147 (i+1))
      = (∑ i ∈ Finset.range 202, stT147 (i+1)) + stT147 203 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 202
    simpa using h
  have hprev := st147_p202
  have hstep := st147_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p204 : ((1290312437911/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT147 (i+1))
      = (∑ i ∈ Finset.range 203, stT147 (i+1)) + stT147 204 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 203
    simpa using h
  have hprev := st147_p203
  have hstep := st147_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p205 : ((9719097723579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT147 (i+1))
      = (∑ i ∈ Finset.range 204, stT147 (i+1)) + stT147 205 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 204
    simpa using h
  have hprev := st147_p204
  have hstep := st147_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p206 : ((9034537060027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT147 (i+1))
      = (∑ i ∈ Finset.range 205, stT147 (i+1)) + stT147 206 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 205
    simpa using h
  have hprev := st147_p205
  have hstep := st147_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p207 : ((134407690129/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT147 (i+1))
      = (∑ i ∈ Finset.range 206, stT147 (i+1)) + stT147 207 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 206
    simpa using h
  have hprev := st147_p206
  have hstep := st147_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p208 : ((1078461446657/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT147 (i+1))
      = (∑ i ∈ Finset.range 207, stT147 (i+1)) + stT147 208 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 207
    simpa using h
  have hprev := st147_p207
  have hstep := st147_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p209 : ((1136887761381/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT147 (i+1))
      = (∑ i ∈ Finset.range 208, stT147 (i+1)) + stT147 209 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 208
    simpa using h
  have hprev := st147_p208
  have hstep := st147_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p210 : ((9779565833443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT147 (i+1))
      = (∑ i ∈ Finset.range 209, stT147 (i+1)) + stT147 210 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 209
    simpa using h
  have hprev := st147_p209
  have hstep := st147_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p211 : ((10358659763767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT147 (i+1))
      = (∑ i ∈ Finset.range 210, stT147 (i+1)) + stT147 211 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 210
    simpa using h
  have hprev := st147_p210
  have hstep := st147_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p212 : ((2112911776511/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT147 (i+1))
      = (∑ i ∈ Finset.range 211, stT147 (i+1)) + stT147 212 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 211
    simpa using h
  have hprev := st147_p211
  have hstep := st147_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p213 : ((2576443661367/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT147 (i+1))
      = (∑ i ∈ Finset.range 212, stT147 (i+1)) + stT147 213 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 212
    simpa using h
  have hprev := st147_p212
  have hstep := st147_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p214 : ((4852107090183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT147 (i+1))
      = (∑ i ∈ Finset.range 213, stT147 (i+1)) + stT147 214 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 213
    simpa using h
  have hprev := st147_p213
  have hstep := st147_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p215 : ((4517247545183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT147 (i+1))
      = (∑ i ∈ Finset.range 214, stT147 (i+1)) + stT147 215 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 214
    simpa using h
  have hprev := st147_p214
  have hstep := st147_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p216 : ((17193951921/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT147 (i+1))
      = (∑ i ∈ Finset.range 215, stT147 (i+1)) + stT147 216 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 215
    simpa using h
  have hprev := st147_p215
  have hstep := st147_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p217 : ((1716755978509/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT147 (i+1))
      = (∑ i ∈ Finset.range 216, stT147 (i+1)) + stT147 217 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 216
    simpa using h
  have hprev := st147_p216
  have hstep := st147_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p218 : ((1799422134641/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT147 (i+1))
      = (∑ i ∈ Finset.range 217, stT147 (i+1)) + stT147 218 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 217
    simpa using h
  have hprev := st147_p217
  have hstep := st147_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p219 : ((9653195889771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT147 (i+1))
      = (∑ i ∈ Finset.range 218, stT147 (i+1)) + stT147 219 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 218
    simpa using h
  have hprev := st147_p218
  have hstep := st147_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p220 : ((10266503932887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT147 (i+1))
      = (∑ i ∈ Finset.range 219, stT147 (i+1)) + stT147 220 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 219
    simpa using h
  have hprev := st147_p219
  have hstep := st147_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p221 : ((10574688609687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT147 (i+1))
      = (∑ i ∈ Finset.range 220, stT147 (i+1)) + stT147 221 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 220
    simpa using h
  have hprev := st147_p220
  have hstep := st147_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p222 : ((1306179074031/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT147 (i+1))
      = (∑ i ∈ Finset.range 221, stT147 (i+1)) + stT147 222 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 221
    simpa using h
  have hprev := st147_p221
  have hstep := st147_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p223 : ((4973516183649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT147 (i+1))
      = (∑ i ∈ Finset.range 222, stT147 (i+1)) + stT147 223 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 222
    simpa using h
  have hprev := st147_p222
  have hstep := st147_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p224 : ((4640122037037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT147 (i+1))
      = (∑ i ∈ Finset.range 223, stT147 (i+1)) + stT147 224 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 223
    simpa using h
  have hprev := st147_p223
  have hstep := st147_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p225 : ((4363139231879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT147 (i+1))
      = (∑ i ∈ Finset.range 224, stT147 (i+1)) + stT147 225 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 224
    simpa using h
  have hprev := st147_p224
  have hstep := st147_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p226 : ((4255712215761/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT147 (i+1))
      = (∑ i ∈ Finset.range 225, stT147 (i+1)) + stT147 226 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 225
    simpa using h
  have hprev := st147_p225
  have hstep := st147_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p227 : ((8720284121439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT147 (i+1))
      = (∑ i ∈ Finset.range 226, stT147 (i+1)) + stT147 227 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 226
    simpa using h
  have hprev := st147_p226
  have hstep := st147_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p228 : ((9265165459737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT147 (i+1))
      = (∑ i ∈ Finset.range 227, stT147 (i+1)) + stT147 228 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 227
    simpa using h
  have hprev := st147_p227
  have hstep := st147_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p229 : ((9925451501247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT147 (i+1))
      = (∑ i ∈ Finset.range 228, stT147 (i+1)) + stT147 229 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 228
    simpa using h
  have hprev := st147_p228
  have hstep := st147_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p230 : ((10438390456427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT147 (i+1))
      = (∑ i ∈ Finset.range 229, stT147 (i+1)) + stT147 230 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 229
    simpa using h
  have hprev := st147_p229
  have hstep := st147_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p231 : ((662717185499/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT147 (i+1))
      = (∑ i ∈ Finset.range 230, stT147 (i+1)) + stT147 231 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 230
    simpa using h
  have hprev := st147_p230
  have hstep := st147_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p232 : ((10359120607247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT147 (i+1))
      = (∑ i ∈ Finset.range 231, stT147 (i+1)) + stT147 232 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 231
    simpa using h
  have hprev := st147_p231
  have hstep := st147_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p233 : ((9803068121453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT147 (i+1))
      = (∑ i ∈ Finset.range 232, stT147 (i+1)) + stT147 233 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 232
    simpa using h
  have hprev := st147_p232
  have hstep := st147_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p234 : ((4575511957909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT147 (i+1))
      = (∑ i ∈ Finset.range 233, stT147 (i+1)) + stT147 234 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 233
    simpa using h
  have hprev := st147_p233
  have hstep := st147_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p235 : ((1730345346583/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT147 (i+1))
      = (∑ i ∈ Finset.range 234, stT147 (i+1)) + stT147 235 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 234
    simpa using h
  have hprev := st147_p234
  have hstep := st147_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p236 : ((212307383267/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT147 (i+1))
      = (∑ i ∈ Finset.range 235, stT147 (i+1)) + stT147 236 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 235
    simpa using h
  have hprev := st147_p235
  have hstep := st147_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p237 : ((8729680971299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT147 (i+1))
      = (∑ i ∈ Finset.range 236, stT147 (i+1)) + stT147 237 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 236
    simpa using h
  have hprev := st147_p236
  have hstep := st147_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p238 : ((4636334154271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT147 (i+1))
      = (∑ i ∈ Finset.range 237, stT147 (i+1)) + stT147 238 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 237
    simpa using h
  have hprev := st147_p237
  have hstep := st147_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p239 : ((4959499062717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT147 (i+1))
      = (∑ i ∈ Finset.range 238, stT147 (i+1)) + stT147 239 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 238
    simpa using h
  have hprev := st147_p238
  have hstep := st147_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p240 : ((5215936946901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT147 (i+1))
      = (∑ i ∈ Finset.range 239, stT147 (i+1)) + stT147 240 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 239
    simpa using h
  have hprev := st147_p239
  have hstep := st147_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p241 : ((5313287276947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT147 (i+1))
      = (∑ i ∈ Finset.range 240, stT147 (i+1)) + stT147 241 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 240
    simpa using h
  have hprev := st147_p240
  have hstep := st147_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p242 : ((10435600888769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT147 (i+1))
      = (∑ i ∈ Finset.range 241, stT147 (i+1)) + stT147 242 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 241
    simpa using h
  have hprev := st147_p241
  have hstep := st147_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p243 : ((4964990353043/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT147 (i+1))
      = (∑ i ∈ Finset.range 242, stT147 (i+1)) + stT147 243 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 242
    simpa using h
  have hprev := st147_p242
  have hstep := st147_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p244 : ((9290889782251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT147 (i+1))
      = (∑ i ∈ Finset.range 243, stT147 (i+1)) + stT147 244 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 243
    simpa using h
  have hprev := st147_p243
  have hstep := st147_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p245 : ((218587770739/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT147 (i+1))
      = (∑ i ∈ Finset.range 244, stT147 (i+1)) + stT147 245 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 244
    simpa using h
  have hprev := st147_p244
  have hstep := st147_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p246 : ((2119405842101/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT147 (i+1))
      = (∑ i ∈ Finset.range 245, stT147 (i+1)) + stT147 246 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 245
    simpa using h
  have hprev := st147_p245
  have hstep := st147_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p247 : ((536429722427/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT147 (i+1))
      = (∑ i ∈ Finset.range 246, stT147 (i+1)) + stT147 247 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 246
    simpa using h
  have hprev := st147_p246
  have hstep := st147_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p248 : ((1127548422979/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT147 (i+1))
      = (∑ i ∈ Finset.range 247, stT147 (i+1)) + stT147 248 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 247
    simpa using h
  have hprev := st147_p247
  have hstep := st147_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p249 : ((481946589643/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT147 (i+1))
      = (∑ i ∈ Finset.range 248, stT147 (i+1)) + stT147 249 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 248
    simpa using h
  have hprev := st147_p248
  have hstep := st147_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_p250 : ((2045706201921/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT147 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT147 (i+1))
      = (∑ i ∈ Finset.range 249, stT147 (i+1)) + stT147 250 := by
    have h := Finset.sum_range_succ (fun i => stT147 (i+1)) 249
    simpa using h
  have hprev := st147_p249
  have hstep := st147_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st147_s250 :
    |Real.sin (((147 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((188437/250000 : ℚ) : ℝ))
      - ((72343/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 231317/2500000) (δ := 941/125000000) (ψ := 188437/250000) 147 129
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 147`** (evaluated boundary). -/
theorem station_147_sign : 0 < hardyG ((((147:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 147 250 (by norm_num) (by norm_num)
    ((188437/250000 : ℚ) : ℝ)
  have hchain := st147_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT147 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((147 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((188437/250000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st147_c250
  have hsinb := abs_le.mp st147_s250
  have hbdy_lo : ((-652471097861/16622500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((147 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((188437/250000 : ℚ) : ℝ))) / 2
          - ((((147:ℕ)):ℝ))
            * Real.sin (((147 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((188437/250000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((147:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((147:ℝ) * Real.log (250:ℝ) - ((188437/250000 : ℚ) : ℝ))) / 2
        - ((147:ℝ)) * Real.sin ((147:ℝ) * Real.log (250:ℝ) - ((188437/250000 : ℚ) : ℝ))
        ≥ ((-107291249/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((147:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-107291249/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-107291249/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-107291249/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((147:ℕ)):ℝ))+1) * (((((147:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((234051331723/468750000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((2045706201921/2000000000000 : ℚ) : ℝ) + ((-652471097861/16622500000000 : ℚ) : ℝ)
      - ((234051331723/468750000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((188437/250000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((147:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((188437/250000 : ℚ) : ℝ)
        * (riemannZeta (line ((((147:ℕ)):ℝ)))).re
      - Real.sin ((188437/250000 : ℚ) : ℝ)
        * (riemannZeta (line ((((147:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((147:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((147:ℕ)):ℝ))
      = (((((147:ℕ)):ℝ)) * (Real.log ((((147:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((147:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_147
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
  have hθwin : |(((188437/250000 : ℚ) : ℝ) + ((25:ℤ)) * (2*Real.pi)) - theta ((((147:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((147:ℕ)):ℝ)))
    (φ := ((188437/250000 : ℚ) : ℝ) + ((25:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((188437/250000 : ℚ)) : ℝ) 25).1,
    (cos_sin_shift (((188437/250000 : ℚ)) : ℝ) 25).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_147_sign
end AxiomAudit
