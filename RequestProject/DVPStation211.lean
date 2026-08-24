import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 211` (rung-217.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT211 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((211 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((95177/100000 : ℚ) : ℝ))

theorem st211_c1 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((290121/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -95177/400000) (δ := 1/1000000000) (ψ := 95177/100000) 211 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t1 : ((18131/31250 : ℚ) : ℝ) ≤ stT211 1 := by
  have hc : ((18131/31250 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18131/31250 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((18131/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c2 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((22017/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1972541/10000000) (δ := 671/62500000) (ψ := 95177/100000) 211 23
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t2 : ((2490762137549/5000000000000 : ℚ) : ℝ) ≤ stT211 2 := by
  have hc : ((352247/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2490762137549/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((352247/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c3 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-25811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -507013/1250000) (δ := 10567/1000000000) (ψ := 95177/100000) 211 37
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t3 : ((-37291055877/1250000000000 : ℚ) : ℝ) ≤ stT211 3 := by
  have hc : ((-6459/125000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37291055877/1250000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-6459/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c4 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-204657/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3162267/5000000) (δ := 10671/1000000000) (ψ := 95177/100000) 211 46
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t4 : ((-2046695409339/5000000000000 : ℚ) : ℝ) ≤ stT211 4 := by
  have hc : ((-409339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2046695409339/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-409339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c5 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((99331/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1630923/10000000) (δ := 5307/500000000) (ψ := 95177/100000) 211 54
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t5 : ((355354952673/1000000000000 : ℚ) : ℝ) ≤ stT211 5 := by
  have hc : ((397299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((355354952673/1000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((397299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c6 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((248251/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 295889/10000000) (δ := 1329/125000000) (ψ := 95177/100000) 211 60
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t6 : ((1013429207957/2500000000000 : ℚ) : ℝ) ≤ stT211 6 := by
  have hc : ((496477/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1013429207957/2500000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((496477/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c7 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((83977/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3070567/10000000) (δ := 2667/250000000) (ψ := 95177/100000) 211 65
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t7 : ((158677959319/1250000000000 : ℚ) : ℝ) ≤ stT211 7 := by
  have hc : ((167929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158677959319/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((167929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c8 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-106887/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1257859/2500000) (δ := 2651/250000000) (ψ := 95177/100000) 211 70
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t8 : ((-377946816833/2500000000000 : ℚ) : ℝ) ≤ stT211 8 := by
  have hc : ((-213799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-377946816833/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-213799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c9 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-661117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5732757/10000000) (δ := 1067/100000000) (ψ := 95177/100000) 211 74
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t9 : ((-1101945220389/5000000000000 : ℚ) : ℝ) ≤ stT211 9 := by
  have hc : ((-661167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1101945220389/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-661167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c10 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((463897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2721017/10000000) (δ := 10649/1000000000) (ψ := 95177/100000) 211 77
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t10 : ((1466812699619/10000000000000 : ℚ) : ℝ) ≤ stT211 10 := by
  have hc : ((463847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1466812699619/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((463847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c11 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-702217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2936629/5000000) (δ := 661/62500000) (ψ := 95177/100000) 211 80
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t11 : ((-1058707531719/5000000000000 : ℚ) : ℝ) ≤ stT211 11 := by
  have hc : ((-702267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1058707531719/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-702267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c12 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-284377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2323941/5000000) (δ := 10697/1000000000) (ψ := 95177/100000) 211 83
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t12 : ((-25658444097/312500000000 : ℚ) : ℝ) ≤ stT211 12 := by
  have hc : ((-284427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25658444097/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-284427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c13 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((62179/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63371/2500000) (δ := 1323/125000000) (ψ := 95177/100000) 211 86
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t13 : ((2759116629/10000000000 : ℚ) : ℝ) ≤ stT211 13 := by
  have hc : ((497407/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2759116629/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((497407/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c14 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-985147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 46391/62500) (δ := 10733/1000000000) (ψ := 95177/100000) 211 88
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t14 : ((-2633050309761/10000000000000 : ℚ) : ℝ) ≤ stT211 14 := by
  have hc : ((-985197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2633050309761/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-985197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c15 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((245239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -413447/1250000) (δ := 2687/250000000) (ψ := 95177/100000) 211 91
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t15 : ((158268763933/2500000000000 : ℚ) : ℝ) ≤ stT211 15 := by
  have hc : ((245189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158268763933/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((245189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c16 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((192659/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -679443/10000000) (δ := 10669/1000000000) (ψ := 95177/100000) 211 93
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t16 : ((192649/800000 : ℚ) : ℝ) ≤ stT211 16 := by
  have hc : ((192649/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192649/800000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((192649/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c17 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((499463/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115893/10000000) (δ := 2671/250000000) (ψ := 95177/100000) 211 95
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t17 : ((151414368741/625000000000 : ℚ) : ℝ) ≤ stT211 17 := by
  have hc : ((249719/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151414368741/625000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((249719/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c18 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((851317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -345191/2500000) (δ := 2121/200000000) (ψ := 95177/100000) 211 97
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t18 : ((1003227523437/5000000000000 : ℚ) : ℝ) ≤ stT211 18 := by
  have hc : ((851267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1003227523437/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((851267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c19 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-139247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2138121/5000000) (δ := 1339/125000000) (ψ := 95177/100000) 211 99
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t19 : ((-159784663463/5000000000000 : ℚ) : ℝ) ≤ stT211 19 := by
  have hc : ((-139297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159784663463/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-139297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c20 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-475801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 707301/1000000) (δ := 1323/125000000) (ψ := 95177/100000) 211 100
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t20 : ((-132997411521/625000000000 : ℚ) : ℝ) ≤ stT211 20 := by
  have hc : ((-237913/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132997411521/625000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-237913/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c21 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((424273/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 696957/5000000) (δ := 10569/1000000000) (ψ := 95177/100000) 211 102
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t21 : ((57861540759/312500000000 : ℚ) : ℝ) ≤ stT211 21 := by
  have hc : ((53031/62500 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57861540759/312500000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((53031/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c22 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-36431/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -685339/1250000) (δ := 2687/250000000) (ψ := 95177/100000) 211 104
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t22 : ((-77677845973/625000000000 : ℚ) : ℝ) ≤ stT211 22 := by
  have hc : ((-291473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77677845973/625000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-291473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c23 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((61921/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2257649/10000000) (δ := 2131/200000000) (ψ := 95177/100000) 211 105
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t23 : ((4034492997/31250000000 : ℚ) : ℝ) ≤ stT211 23 := by
  have hc : ((15479/25000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4034492997/31250000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((15479/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c24 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-896781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6708089/10000000) (δ := 10633/1000000000) (ψ := 95177/100000) 211 107
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t24 : ((-915324552051/5000000000000 : ℚ) : ℝ) ≤ stT211 24 := by
  have hc : ((-896831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-915324552051/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-896831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c25 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((938347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -882447/10000000) (δ := 10577/1000000000) (ψ := 95177/100000) 211 108
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t25 : ((938297/5000000 : ℚ) : ℝ) ≤ stT211 25 := by
  have hc : ((938297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((938297/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((938297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c26 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-68553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4098509/10000000) (δ := 1323/125000000) (ψ := 95177/100000) 211 109
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t26 : ((-67270798343/5000000000000 : ℚ) : ℝ) ≤ stT211 26 := by
  have hc : ((-68603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67270798343/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-68603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c27 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-98423/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7409409/10000000) (δ := 5349/500000000) (ψ := 95177/100000) 211 111
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t27 : ((-47356196107/250000000000 : ℚ) : ℝ) ≤ stT211 27 := by
  have hc : ((-24607/25000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47356196107/250000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-24607/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c28 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-321/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3933411/10000000) (δ := 10597/1000000000) (ψ := 95177/100000) 211 112
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t28 : ((-2473778307/5000000000000 : ℚ) : ℝ) ≤ stT211 28 := by
  have hc : ((-1309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2473778307/5000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-1309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c29 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((899451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1130713/10000000) (δ := 10713/1000000000) (ψ := 95177/100000) 211 113
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t29 : ((1670145385153/10000000000000 : ℚ) : ℝ) ≤ stT211 29 := by
  have hc : ((899401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1670145385153/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((899401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c30 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((457003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 208873/2000000) (δ := 67/6250000) (ψ := 95177/100000) 211 114
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t30 : ((417161735349/2500000000000 : ℚ) : ℝ) ≤ stT211 30 := by
  have hc : ((228489/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((417161735349/2500000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((228489/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c31 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((494767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1316537/5000000) (δ := 10727/1000000000) (ψ := 95177/100000) 211 115
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t31 : ((888537952001/10000000000000 : ℚ) : ℝ) ≤ stT211 31 := by
  have hc : ((494717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((888537952001/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((494717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c32 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((101601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73451/200000) (δ := 5367/500000000) (ψ := 95177/100000) 211 116
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t32 : ((89759202533/5000000000000 : ℚ) : ℝ) ≤ stT211 32 := by
  have hc : ((101551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89759202533/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((101551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c33 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-107637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 839321/2000000) (δ := 10661/1000000000) (ψ := 95177/100000) 211 117
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t33 : ((-187459052799/10000000000000 : ℚ) : ℝ) ≤ stT211 33 := by
  have hc : ((-107687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187459052799/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-107687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c34 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-123329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42361/100000) (δ := 10749/1000000000) (ψ := 95177/100000) 211 118
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t34 : ((-105796628847/5000000000000 : ℚ) : ℝ) ≤ stT211 34 := by
  have hc : ((-123379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105796628847/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-123379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c35 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((21583/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1909521/5000000) (δ := 10747/1000000000) (ψ := 95177/100000) 211 119
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t35 : ((4554957483/625000000000 : ℚ) : ℝ) ≤ stT211 35 := by
  have hc : ((10779/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4554957483/625000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((10779/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c36 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((18653/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2971229/10000000) (δ := 10563/1000000000) (ψ := 95177/100000) 211 120
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t36 : ((31084154233/500000000000 : ℚ) : ℝ) ≤ stT211 36 := by
  have hc : ((37301/100000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31084154233/500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((37301/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c37 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((24171/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 858119/5000000) (δ := 10633/1000000000) (ψ := 95177/100000) 211 121
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t37 : ((635748630179/5000000000000 : ℚ) : ℝ) ≤ stT211 37 := by
  have hc : ((386711/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((635748630179/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((386711/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c38 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((999541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 303/40000) (δ := 5363/500000000) (ψ := 95177/100000) 211 122
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t38 : ((810694146537/5000000000000 : ℚ) : ℝ) ≤ stT211 38 := by
  have hc : ((999491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((810694146537/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((999491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c39 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((716479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1930137/10000000) (δ := 5359/500000000) (ψ := 95177/100000) 211 123
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t39 : ((1147204145549/10000000000000 : ℚ) : ℝ) ≤ stT211 39 := by
  have hc : ((716429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1147204145549/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((716429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c40 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-141907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53537/125000) (δ := 2673/250000000) (ψ := 95177/100000) 211 124
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t40 : ((-224453749023/10000000000000 : ℚ) : ℝ) ≤ stT211 40 := by
  have hc : ((-141957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224453749023/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-141957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c41 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-937521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6965577/10000000) (δ := 10599/1000000000) (ψ := 95177/100000) 211 125
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t41 : ((-732120129199/5000000000000 : ℚ) : ℝ) ≤ stT211 41 := by
  have hc : ((-937571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-732120129199/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-937571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c42 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-332527/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5745907/10000000) (δ := 10599/1000000000) (ψ := 95177/100000) 211 125
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t42 : ((-32071190173/312500000000 : ℚ) : ℝ) ≤ stT211 42 := by
  have hc : ((-41569/62500 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32071190173/312500000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-41569/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c43 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((556929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1225141/5000000) (δ := 10697/1000000000) (ψ := 95177/100000) 211 126
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t43 : ((169846424363/2000000000000 : ℚ) : ℝ) ≤ stT211 43 := by
  have hc : ((556879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169846424363/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((556879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c44 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((17989/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7067/62500) (δ := 1069/100000000) (ψ := 95177/100000) 211 127
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t44 : ((1694869833/12500000000 : ℚ) : ℝ) ≤ stT211 44 := by
  have hc : ((4497/5000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1694869833/12500000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((4497/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c45 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-410421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4984281/10000000) (δ := 10583/1000000000) (ψ := 95177/100000) 211 128
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t45 : ((-76486755669/1250000000000 : ℚ) : ℝ) ≤ stT211 45 := by
  have hc : ((-410471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76486755669/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-410471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c46 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-13729/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6609589/10000000) (δ := 531/50000000) (ψ := 95177/100000) 211 128
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t46 : ((-32389542513/250000000000 : ℚ) : ℝ) ≤ stT211 46 := by
  have hc : ((-439353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32389542513/250000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-439353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c47 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((1557/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2246199/10000000) (δ := 2657/250000000) (ψ := 95177/100000) 211 129
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t47 : ((3633494659/40000000000 : ℚ) : ℝ) ≤ stT211 47 := by
  have hc : ((2491/4000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3633494659/40000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((2491/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c48 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((587817/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18407/78125) (δ := 1321/125000000) (ψ := 95177/100000) 211 130
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t48 : ((6786945549/80000000000 : ℚ) : ℝ) ≤ stT211 48 := by
  have hc : ((587767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6786945549/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((587767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c49 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-964667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7187431/10000000) (δ := 5321/500000000) (ψ := 95177/100000) 211 131
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t49 : ((-344541923531/2500000000000 : ℚ) : ℝ) ≤ stT211 49 := by
  have hc : ((-964717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-344541923531/2500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-964717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c50 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((181959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1734773/5000000) (δ := 5321/500000000) (ψ := 95177/100000) 211 131
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t50 : ((257258072617/10000000000000 : ℚ) : ℝ) ≤ stT211 50 := by
  have hc : ((181909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((257258072617/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((181909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c51 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((94221/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -896273/5000000) (δ := 5277/500000000) (ψ := 95177/100000) 211 132
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t51 : ((13192703013/125000000000 : ℚ) : ℝ) ≤ stT211 51 := by
  have hc : ((376859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13192703013/125000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((376859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c52 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-242917/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3628731/5000000) (δ := 10747/1000000000) (ψ := 95177/100000) 211 133
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t52 : ((-673765454109/5000000000000 : ℚ) : ℝ) ≤ stT211 52 := by
  have hc : ((-485859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-673765454109/5000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-485859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c53 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((439113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 43601/156250) (δ := 2639/250000000) (ψ := 95177/100000) 211 133
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t53 : ((120619826423/2000000000000 : ℚ) : ℝ) ≤ stT211 53 := by
  have hc : ((439063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120619826423/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((439063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c54 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((170429/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3057417/10000000) (δ := 10739/1000000000) (ψ := 95177/100000) 211 134
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t54 : ((57972591027/1250000000000 : ℚ) : ℝ) ≤ stT211 54 := by
  have hc : ((42601/125000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57972591027/1250000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((42601/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c55 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-176193/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3310867/5000000) (δ := 1333/125000000) (ψ := 95177/100000) 211 134
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t55 : ((-593980313/5000000000 : ℚ) : ℝ) ≤ stT211 55 := by
  have hc : ((-176203/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-593980313/5000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-176203/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c56 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((986019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 418529/10000000) (δ := 1329/125000000) (ψ := 95177/100000) 211 135
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t56 : ((658778145257/5000000000000 : ℚ) : ℝ) ≤ stT211 56 := by
  have hc : ((985969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((658778145257/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((985969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c57 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-724537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1190579/2000000) (δ := 5289/500000000) (ψ := 95177/100000) 211 136
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t57 : ((-959739392871/10000000000000 : ℚ) : ℝ) ≤ stT211 57 := by
  have hc : ((-724587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-959739392871/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-724587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c58 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((278551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3221279/10000000) (δ := 429/40000000) (ψ := 95177/100000) 211 136
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t58 : ((45711204633/1250000000000 : ℚ) : ℝ) ≤ stT211 58 := by
  have hc : ((278501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45711204633/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((278501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c59 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((182021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -867347/2500000) (δ := 5309/500000000) (ψ := 95177/100000) 211 137
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t59 : ((236906043219/10000000000000 : ℚ) : ℝ) ≤ stT211 59 := by
  have hc : ((181971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((236906043219/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((181971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c60 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-554487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5396357/10000000) (δ := 5359/500000000) (ψ := 95177/100000) 211 137
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t60 : ((-143180898863/2000000000000 : ℚ) : ℝ) ≤ stT211 60 := by
  have hc : ((-554537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143180898863/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-554537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c61 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((200977/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3981/25000) (δ := 331/31250000) (ψ := 95177/100000) 211 138
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t61 : ((32163564367/312500000000 : ℚ) : ℝ) ≤ stT211 61 := by
  have hc : ((401929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32163564367/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((401929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c62 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-940197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3492507/5000000) (δ := 2673/250000000) (ψ := 95177/100000) 211 138
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t62 : ((-597057785247/5000000000000 : ℚ) : ℝ) ≤ stT211 62 := by
  have hc : ((-940247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-597057785247/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-940247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c63 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((248403/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -282739/10000000) (δ := 669/62500000) (ψ := 95177/100000) 211 139
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t63 : ((625884943061/5000000000000 : ℚ) : ℝ) ≤ stT211 63 := by
  have hc : ((496781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((625884943061/5000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((496781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c64 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-39907/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3841737/5000000) (δ := 1337/125000000) (ψ := 95177/100000) 211 140
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t64 : ((-49886289909/400000000000 : ℚ) : ℝ) ≤ stT211 64 := by
  have hc : ((-39909/40000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49886289909/400000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-39909/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c65 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((980463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30937/625000) (δ := 10607/1000000000) (ψ := 95177/100000) 211 140
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t65 : ((1216052323311/10000000000000 : ℚ) : ℝ) ≤ stT211 65 := by
  have hc : ((980413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1216052323311/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((980413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c66 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-60103/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1431873/2000000) (δ := 5307/500000000) (ψ := 95177/100000) 211 141
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t66 : ((-118376849367/1000000000000 : ℚ) : ℝ) ≤ stT211 66 := by
  have hc : ((-480849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118376849367/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-480849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c67 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((476281/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 773127/10000000) (δ := 10589/1000000000) (ψ := 95177/100000) 211 141
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t67 : ((9091235901/78125000000 : ℚ) : ℝ) ≤ stT211 67 := by
  have hc : ((14883/15625 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9091235901/78125000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((14883/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c68 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-191439/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7119871/10000000) (δ := 5291/500000000) (ψ := 95177/100000) 211 142
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t68 : ((-232166181871/2000000000000 : ℚ) : ℝ) ≤ stT211 68 := by
  have hc : ((-191449/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232166181871/2000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-191449/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c69 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((973117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 145249/2500000) (δ := 5291/500000000) (ψ := 95177/100000) 211 142
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t69 : ((585717246243/5000000000000 : ℚ) : ℝ) ≤ stT211 69 := by
  have hc : ((973067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((585717246243/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((973067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c70 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-991969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -235529/312500) (δ := 423/40000000) (ψ := 95177/100000) 211 143
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t70 : ((-1185689877351/10000000000000 : ℚ) : ℝ) ≤ stT211 70 := by
  have hc : ((-992019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1185689877351/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-992019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c71 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((499881/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54551/10000000) (δ := 1341/125000000) (ψ := 95177/100000) 211 143
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t71 : ((37076225221/312500000000 : ℚ) : ℝ) ≤ stT211 71 := by
  have hc : ((31241/31250 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37076225221/312500000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((31241/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c72 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-244387/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3661611/5000000) (δ := 2657/250000000) (ψ := 95177/100000) 211 143
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t72 : ((-36003467943/312500000000 : ℚ) : ℝ) ≤ stT211 72 := by
  have hc : ((-488799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36003467943/312500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-488799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c73 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((903251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -138597/1250000) (δ := 2667/250000000) (ψ := 95177/100000) 211 144
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t73 : ((1057116385611/10000000000000 : ℚ) : ℝ) ≤ stT211 73 := by
  have hc : ((903201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1057116385611/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((903201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c74 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-377769/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3034089/5000000) (δ := 2667/250000000) (ψ := 95177/100000) 211 144
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t74 : ((-219588417869/2500000000000 : ℚ) : ℝ) ≤ stT211 74 := by
  have hc : ((-188897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219588417869/2500000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-188897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c75 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((520261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25591/100000) (δ := 533/50000000) (ψ := 95177/100000) 211 145
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t75 : ((6006876417/100000000000 : ℚ) : ℝ) ≤ stT211 75 := by
  have hc : ((520211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6006876417/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((520211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c76 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-49741/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4427743/10000000) (δ := 533/50000000) (ψ := 95177/100000) 211 145
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t76 : ((-114142390053/5000000000000 : ℚ) : ℝ) ≤ stT211 76 := by
  have hc : ((-99507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114142390053/5000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-99507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c77 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-182057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4384687/10000000) (δ := 213/20000000) (ψ := 95177/100000) 211 146
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t77 : ((-103765114921/5000000000000 : ℚ) : ℝ) ≤ stT211 77 := by
  have hc : ((-182107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103765114921/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-182107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c78 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((8849/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75683/312500) (δ := 10653/1000000000) (ψ := 95177/100000) 211 146
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t78 : ((320596306611/5000000000000 : ℚ) : ℝ) ≤ stT211 78 := by
  have hc : ((283143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320596306611/5000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((283143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c79 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-435127/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1313257/2000000) (δ := 5373/500000000) (ψ := 95177/100000) 211 147
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t79 : ((-956219323/9765625000 : ℚ) : ℝ) ≤ stT211 79 := by
  have hc : ((-27197/31250 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-956219323/9765625000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-27197/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c80 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((999619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8629/1250000) (δ := 5373/500000000) (ψ := 95177/100000) 211 147
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t80 : ((1117551127777/10000000000000 : ℚ) : ℝ) ≤ stT211 80 := by
  have hc : ((999569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1117551127777/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((999569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c81 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-220249/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6621901/10000000) (δ := 5323/500000000) (ψ := 95177/100000) 211 147
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t81 : ((-61183798947/625000000000 : ℚ) : ℝ) ≤ stT211 81 := by
  have hc : ((-440523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61183798947/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-440523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c82 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((501527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -163349/625000) (δ := 1333/125000000) (ψ := 95177/100000) 211 148
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t82 : ((110757714651/2000000000000 : ℚ) : ℝ) ≤ stT211 82 := by
  have hc : ((501477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110757714651/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((501477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c83 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((58581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1890227/5000000) (δ := 10639/1000000000) (ψ := 95177/100000) 211 148
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t83 : ((32123041951/5000000000000 : ℚ) : ℝ) ≤ stT211 83 := by
  have hc : ((58531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32123041951/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((58531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c84 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-311761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -561009/1000000) (δ := 5283/250000000) (ψ := 95177/100000) 211 149
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t84 : ((-17009329337/250000000000 : ℚ) : ℝ) ≤ stT211 84 := by
  have hc : ((-155893/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17009329337/250000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-155893/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c85 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((484079/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 316291/5000000) (δ := 2683/250000000) (ψ := 95177/100000) 211 149
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t85 : ((65628767401/625000000000 : ℚ) : ℝ) ≤ stT211 85 := by
  have hc : ((242027/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65628767401/625000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((242027/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c86 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-456401/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3401111/5000000) (δ := 2683/250000000) (ψ := 95177/100000) 211 149
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t86 : ((-30761058483/312500000000 : ℚ) : ℝ) ≤ stT211 86 := by
  have hc : ((-228213/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30761058483/312500000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-228213/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c87 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((433029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1403683/5000000) (δ := 5289/500000000) (ψ := 95177/100000) 211 150
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t87 : ((29012623853/625000000000 : ℚ) : ℝ) ≤ stT211 87 := by
  have hc : ((432979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29012623853/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((432979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c88 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((278553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3221273/10000000) (δ := 17/1600000) (ψ := 95177/100000) 211 150
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t88 : ((296885033509/10000000000000 : ℚ) : ℝ) ≤ stT211 88 := by
  have hc : ((278503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((296885033509/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((278503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c89 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-172449/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1631551/2500000) (δ := 10617/1000000000) (ψ := 95177/100000) 211 151
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t89 : ((-91403097541/1000000000000 : ℚ) : ℝ) ≤ stT211 89 := by
  have hc : ((-172459/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91403097541/1000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-172459/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c90 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((968187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19759/312500) (δ := 5293/500000000) (ψ := 95177/100000) 211 151
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t90 : ((255126366651/2500000000000 : ℚ) : ℝ) ≤ stT211 90 := by
  have hc : ((968137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((255126366651/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((968137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c91 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-243131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1299127/2500000) (δ := 10593/500000000) (ψ := 95177/100000) 211 151
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t91 : ((-12744839373/250000000000 : ℚ) : ℝ) ≤ stT211 91 := by
  have hc : ((-60789/125000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12744839373/250000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-60789/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c92 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-1006/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2373191/5000000) (δ := 1071/100000000) (ψ := 95177/100000) 211 152
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t92 : ((-33567722881/1000000000000 : ℚ) : ℝ) ≤ stT211 92 := by
  have hc : ((-32197/100000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33567722881/1000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-32197/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c93 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((927717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 59773/625000) (δ := 1061/100000000) (ψ := 95177/100000) 211 152
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t93 : ((961945223317/10000000000000 : ℚ) : ℝ) ≤ stT211 93 := by
  have hc : ((927667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((961945223317/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((927667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c94 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-43823/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6598139/10000000) (δ := 10593/1000000000) (ψ := 95177/100000) 211 152
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t94 : ((-45202584861/500000000000 : ℚ) : ℝ) ≤ stT211 94 := by
  have hc : ((-87651/100000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45202584861/500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-87651/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c95 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((39753/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3527767/10000000) (δ := 10703/1000000000) (ψ := 95177/100000) 211 153
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t95 : ((40772878709/2500000000000 : ℚ) : ℝ) ≤ stT211 95 := by
  have hc : ((79481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40772878709/2500000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((79481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c96 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((348949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 498961/2500000) (δ := 10603/1000000000) (ψ := 95177/100000) 211 153
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t96 : ((4451485161/62500000000 : ℚ) : ℝ) ≤ stT211 96 := by
  have hc : ((87231/125000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4451485161/62500000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((87231/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c97 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-987747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7462221/10000000) (δ := 10603/1000000000) (ψ := 95177/100000) 211 153
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t97 : ((-1002956720559/10000000000000 : ℚ) : ℝ) ≤ stT211 97 := by
  have hc : ((-987797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1002956720559/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-987797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c98 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((2643/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1417719/5000000) (δ := 10707/1000000000) (ψ := 95177/100000) 211 154
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t98 : ((5339032127/125000000000 : ℚ) : ℝ) ≤ stT211 98 := by
  have hc : ((42283/100000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5339032127/125000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((42283/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c99 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((533569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2519953/10000000) (δ := 10707/1000000000) (ψ := 95177/100000) 211 154
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t99 : ((536206335203/10000000000000 : ℚ) : ℝ) ≤ stT211 99 := by
  have hc : ((533519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((536206335203/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((533519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c100 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-249979/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3910743/5000000) (δ := 10607/1000000000) (ψ := 95177/100000) 211 154
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t100 : ((-499983/5000000 : ℚ) : ℝ) ≤ stT211 100 := by
  have hc : ((-499983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-499983/5000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-499983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c101 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((493179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2637641/10000000) (δ := 5357/500000000) (ψ := 95177/100000) 211 155
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t101 : ((490681600773/10000000000000 : ℚ) : ℝ) ≤ stT211 101 := by
  have hc : ((493129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((490681600773/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((493129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c102 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((260071/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2559447/10000000) (δ := 5307/500000000) (ψ := 95177/100000) 211 155
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t102 : ((128741883381/2500000000000 : ℚ) : ℝ) ≤ stT211 102 := by
  have hc : ((130023/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128741883381/2500000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((130023/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c103 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-249561/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 770579/1000000) (δ := 5357/500000000) (ψ := 95177/100000) 211 155
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t103 : ((-49182451351/500000000000 : ℚ) : ℝ) ≤ stT211 103 := by
  have hc : ((-499147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49182451351/500000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-499147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c104 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((198657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2905521/10000000) (δ := 5361/500000000) (ψ := 95177/100000) 211 156
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t104 : ((1217341041/31250000000 : ℚ) : ℝ) ≤ stT211 104 := by
  have hc : ((24829/62500 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1217341041/31250000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((24829/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c105 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((654741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 214239/1000000) (δ := 5311/500000000) (ψ := 95177/100000) 211 156
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t105 : ((6389129469/100000000000 : ℚ) : ℝ) ≤ stT211 105 := by
  have hc : ((654691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6389129469/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((654691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c106 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-191953/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1785601/2500000) (δ := 10581/1000000000) (ψ := 95177/100000) 211 156
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t106 : ((-93225487209/1000000000000 : ℚ) : ℝ) ≤ stT211 106 := by
  have hc : ((-191963/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93225487209/1000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-191963/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c107 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((125489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -90311/250000) (δ := 5337/500000000) (ψ := 95177/100000) 211 157
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t107 : ((7579149819/625000000000 : ℚ) : ℝ) ≤ stT211 107 := by
  have hc : ((125439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7579149819/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((125439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c108 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((173779/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80911/625000) (δ := 5337/500000000) (ψ := 95177/100000) 211 157
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t108 : ((668836881/8000000000 : ℚ) : ℝ) ≤ stT211 108 := by
  have hc : ((173769/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((668836881/8000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((173769/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c109 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-194541/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6156333/10000000) (δ := 10629/1000000000) (ψ := 95177/100000) 211 157
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t109 : ((-372697190489/5000000000000 : ℚ) : ℝ) ≤ stT211 109 := by
  have hc : ((-389107/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-372697190489/5000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-389107/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c110 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-317317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4734237/10000000) (δ := 10667/1000000000) (ψ := 95177/100000) 211 158
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t110 : ((-302597691921/10000000000000 : ℚ) : ℝ) ≤ stT211 110 := by
  have hc : ((-317367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-302597691921/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-317367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c111 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((7999/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19793/5000000) (δ := 671/62500000) (ψ := 95177/100000) 211 158
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t111 : ((37959635901/400000000000 : ℚ) : ℝ) ≤ stT211 111 := by
  have hc : ((39993/40000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37959635901/400000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((39993/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c112 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-331047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2385261/5000000) (δ := 10567/1000000000) (ψ := 95177/100000) 211 158
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t112 : ((-19553595529/625000000000 : ℚ) : ℝ) ≤ stT211 112 := by
  have hc : ((-331097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19553595529/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-331097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c113 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-800783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3124247/5000000) (δ := 533/50000000) (ψ := 95177/100000) 211 159
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t113 : ((-753360420593/10000000000000 : ℚ) : ℝ) ≤ stT211 113 := by
  have hc : ((-800833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-753360420593/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-800833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c114 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((20047/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -800451/5000000) (δ := 10643/1000000000) (ψ := 95177/100000) 211 159
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t114 : ((15019639011/200000000000 : ℚ) : ℝ) ≤ stT211 114 := by
  have hc : ((80183/100000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15019639011/200000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((80183/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c115 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((360073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24049/80000) (δ := 10743/1000000000) (ψ := 95177/100000) 211 159
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t115 : ((41965360949/1250000000000 : ℚ) : ℝ) ≤ stT211 115 := by
  have hc : ((360023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41965360949/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((360023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c116 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-9937/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 378661/500000) (δ := 10743/1000000000) (ψ := 95177/100000) 211 159
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t116 : ((-147627843/1600000000 : ℚ) : ℝ) ≤ stT211 116 := by
  have hc : ((-159/160 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147627843/1600000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-159/160 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c117 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((127731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3606789/10000000) (δ := 213/20000000) (ψ := 95177/100000) 211 160
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t117 : ((236082169/20000000000 : ℚ) : ℝ) ≤ stT211 117 := by
  have hc : ((127681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((236082169/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((127681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c118 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((37533/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 176521/2000000) (δ := 10553/1000000000) (ψ := 95177/100000) 211 160
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t118 : ((17275031397/200000000000 : ℚ) : ℝ) ≤ stT211 118 := by
  have hc : ((37531/40000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17275031397/200000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((37531/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c119 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-33349/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 666759/1250000) (δ := 10553/1000000000) (ψ := 95177/100000) 211 160
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t119 : ((-244590877083/5000000000000 : ℚ) : ℝ) ≤ stT211 119 := by
  have hc : ((-266817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244590877083/5000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-266817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c120 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-363193/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5959613/10000000) (δ := 10557/1000000000) (ψ := 95177/100000) 211 161
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t120 : ((-165785589439/2500000000000 : ℚ) : ℝ) ≤ stT211 120 := by
  have hc : ((-181609/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165785589439/2500000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-181609/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c121 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((100797/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -395499/2500000) (δ := 10557/1000000000) (ψ := 95177/100000) 211 161
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t121 : ((36651145167/500000000000 : ℚ) : ℝ) ≤ stT211 121 := by
  have hc : ((403163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36651145167/500000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((403163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c122 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((450173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2759593/10000000) (δ := 10657/1000000000) (ψ := 95177/100000) 211 161
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t122 : ((407522008911/10000000000000 : ℚ) : ℝ) ≤ stT211 122 := by
  have hc : ((450123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((407522008911/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((450123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c123 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-59419/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7065733/10000000) (δ := 5373/500000000) (ψ := 95177/100000) 211 161
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t123 : ((-42863317959/500000000000 : ℚ) : ℝ) ≤ stT211 123 := by
  have hc : ((-475377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42863317959/500000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-475377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c124 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-35331/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4370957/10000000) (δ := 5319/500000000) (ψ := 95177/100000) 211 162
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t124 : ((-31737172207/2000000000000 : ℚ) : ℝ) ≤ stT211 124 := by
  have hc : ((-35341/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31737172207/2000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-35341/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c125 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((249641/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -133971/10000000) (δ := 2133/200000000) (ψ := 95177/100000) 211 162
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t125 : ((446548940739/5000000000000 : ℚ) : ℝ) ≤ stT211 125 := by
  have hc : ((499257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((446548940739/5000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((499257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c126 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-91/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2034627/5000000) (δ := 5319/500000000) (ψ := 95177/100000) 211 162
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t126 : ((-2028513267/400000000000 : ℚ) : ℝ) ≤ stT211 126 := by
  have hc : ((-2277/40000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2028513267/400000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-2277/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c127 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-123519/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7468769/10000000) (δ := 10631/1000000000) (ψ := 95177/100000) 211 163
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t127 : ((-438443981057/5000000000000 : ℚ) : ℝ) ≤ stT211 127 := by
  have hc : ((-494101/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-438443981057/5000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-494101/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c128 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((117979/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3331481/10000000) (δ := 10631/1000000000) (ψ := 95177/100000) 211 163
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t128 : ((52128767691/2500000000000 : ℚ) : ℝ) ≤ stT211 128 := by
  have hc : ((58977/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52128767691/2500000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((58977/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c129 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((952501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 77363/1000000) (δ := 667/62500000) (ψ := 95177/100000) 211 163
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t129 : ((16771709659/200000000000 : ℚ) : ℝ) ≤ stT211 129 := by
  have hc : ((952451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16771709659/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((952451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c130 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-89937/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 969397/2000000) (δ := 667/62500000) (ψ := 95177/100000) 211 163
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t130 : ((-157782037041/5000000000000 : ℚ) : ℝ) ≤ stT211 130 := by
  have hc : ((-179899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157782037041/5000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-179899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c131 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-91549/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6818799/10000000) (δ := 83/7812500) (ψ := 95177/100000) 211 164
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t131 : ((-7999118757/100000000000 : ℚ) : ℝ) ≤ stT211 131 := by
  have hc : ((-45777/50000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7999118757/100000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-45777/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c132 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((216513/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -701843/2500000) (δ := 10679/1000000000) (ψ := 95177/100000) 211 164
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t132 : ((5888392417/156250000000 : ℚ) : ℝ) ≤ stT211 132 := by
  have hc : ((27061/62500 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5888392417/156250000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((27061/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c133 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((89179/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73361/625000) (δ := 10679/1000000000) (ψ := 95177/100000) 211 164
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t133 : ((38661788983/500000000000 : ℚ) : ℝ) ≤ stT211 133 := by
  have hc : ((44587/50000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38661788983/500000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((44587/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c134 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-230553/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2562547/5000000) (δ := 21279/1000000000) (ψ := 95177/100000) 211 164
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t134 : ((-99594593141/2500000000000 : ℚ) : ℝ) ≤ stT211 134 := by
  have hc : ((-115289/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99594593141/2500000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-115289/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c135 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-222069/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3330467/5000000) (δ := 10717/1000000000) (ψ := 95177/100000) 211 165
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t135 : ((-382274660069/5000000000000 : ℚ) : ℝ) ≤ stT211 135 := by
  have hc : ((-444163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-382274660069/5000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-444163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c136 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((55899/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2767931/10000000) (δ := 10617/1000000000) (ψ := 95177/100000) 211 165
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t136 : ((47927585983/1250000000000 : ℚ) : ℝ) ≤ stT211 136 := by
  have hc : ((223571/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47927585983/1250000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((223571/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c137 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((226333/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1096587/10000000) (δ := 5293/500000000) (ψ := 95177/100000) 211 165
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t137 : ((386717006837/5000000000000 : ℚ) : ℝ) ≤ stT211 137 := by
  have hc : ((452641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((386717006837/5000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((452641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c138 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-48951/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 616617/1250000) (δ := 10617/1000000000) (ψ := 95177/100000) 211 165
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t138 : ((-166700807053/5000000000000 : ℚ) : ℝ) ≤ stT211 138 := by
  have hc : ((-195829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166700807053/5000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-195829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c139 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-117203/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6966319/10000000) (δ := 1061/100000000) (ψ := 95177/100000) 211 166
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t139 : ((-397662386193/5000000000000 : ℚ) : ℝ) ≤ stT211 139 := by
  have hc : ((-468837/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-397662386193/5000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-468837/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c140 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((292483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -636987/2000000) (δ := 10593/1000000000) (ψ := 95177/100000) 211 166
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t140 : ((123575459841/5000000000000 : ℚ) : ℝ) ≤ stT211 140 := by
  have hc : ((292433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123575459841/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((292433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c141 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((487083/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 569493/10000000) (δ := 1071/100000000) (ψ := 95177/100000) 211 166
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t141 : ((205088190879/2500000000000 : ℚ) : ℝ) ≤ stT211 141 := by
  have hc : ((243529/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((205088190879/2500000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((243529/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c142 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-73819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4297441/10000000) (δ := 1071/100000000) (ψ := 95177/100000) 211 166
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t142 : ((-7746069451/625000000000 : ℚ) : ℝ) ≤ stT211 142 := by
  have hc : ((-18461/125000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7746069451/625000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-18461/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c143 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-998313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3854369/5000000) (δ := 10603/1000000000) (ψ := 95177/100000) 211 167
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t143 : ((-834874070209/10000000000000 : ℚ) : ℝ) ≤ stT211 143 := by
  have hc : ((-998363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-834874070209/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-998363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c144 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-42311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4032801/10000000) (δ := 107/10000000) (ψ := 95177/100000) 211 167
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t144 : ((-17650430787/5000000000000 : ℚ) : ℝ) ≤ stT211 144 := by
  have hc : ((-42361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17650430787/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-42361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c145 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((494167/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -191119/5000000) (δ := 10703/1000000000) (ψ := 95177/100000) 211 167
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t145 : ((102590550117/1250000000000 : ℚ) : ℝ) ≤ stT211 145 := by
  have hc : ((247071/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102590550117/1250000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((247071/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c146 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((8441/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3243217/10000000) (δ := 10603/1000000000) (ψ := 95177/100000) 211 167
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t146 : ((22350466151/1000000000000 : ℚ) : ℝ) ≤ stT211 146 := by
  have hc : ((135031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22350466151/1000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((135031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c147 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-22987/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6843879/10000000) (δ := 10703/1000000000) (ψ := 95177/100000) 211 167
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t147 : ((-75841639011/1000000000000 : ℚ) : ℝ) ≤ stT211 147 := by
  have hc : ((-91953/100000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75841639011/1000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-91953/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c148 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-517837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -330487/625000) (δ := 663/62500000) (ψ := 95177/100000) 211 168
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t148 : ((-85140104913/2000000000000 : ℚ) : ℝ) ≤ stT211 148 := by
  have hc : ((-517887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85140104913/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-517887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c149 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((96069/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -867777/5000000) (δ := 2677/250000000) (ψ := 95177/100000) 211 168
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t149 : ((314790330981/5000000000000 : ℚ) : ℝ) ≤ stT211 149 := by
  have hc : ((384251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((314790330981/5000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((384251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c150 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((753691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44821/250000) (δ := 2139/200000000) (ψ := 95177/100000) 211 168
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t150 : ((38459053871/625000000000 : ℚ) : ℝ) ≤ stT211 150 := by
  have hc : ((753641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38459053871/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((753641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c151 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-1629/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5297867/10000000) (δ := 663/62500000) (ψ := 95177/100000) 211 168
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t151 : ((-42425261937/1000000000000 : ℚ) : ℝ) ≤ stT211 151 := by
  have hc : ((-52133/100000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42425261937/1000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-52133/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c152 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-466109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6928227/10000000) (δ := 2123/200000000) (ψ := 95177/100000) 211 169
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t152 : ((-47260627059/625000000000 : ℚ) : ℝ) ≤ stT211 152 := by
  have hc : ((-233067/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47260627059/625000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-233067/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c153 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((36419/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3469199/10000000) (δ := 167/15625000) (ψ := 95177/100000) 211 169
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t153 : ((7358732217/500000000000 : ℚ) : ℝ) ≤ stT211 153 := by
  have hc : ((36409/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7358732217/500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((36409/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c154 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((499957/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16347/5000000) (δ := 2143/200000000) (ψ := 95177/100000) 211 169
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t154 : ((50357025513/625000000000 : ℚ) : ℝ) ≤ stT211 154 := by
  have hc : ((124983/125000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50357025513/625000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((124983/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c155 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((4329/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3381549/10000000) (δ := 167/15625000) (ψ := 95177/100000) 211 169
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t155 : ((434541479/25000000000 : ℚ) : ℝ) ≤ stT211 155 := by
  have hc : ((541/2500 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((434541479/25000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((541/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c156 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-227027/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6773849/10000000) (δ := 2647/250000000) (ψ := 95177/100000) 211 169
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t156 : ((-363554264639/5000000000000 : ℚ) : ℝ) ≤ stT211 156 := by
  have hc : ((-454079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-363554264639/5000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-454079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c157 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-608843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1112699/2000000) (δ := 10681/1000000000) (ψ := 95177/100000) 211 170
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t157 : ((-485949587691/10000000000000 : ℚ) : ℝ) ≤ stT211 157 := by
  have hc : ((-608893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-485949587691/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-608893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c158 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((126547/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -553573/2500000) (δ := 10681/1000000000) (ψ := 95177/100000) 211 170
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t158 : ((100667396109/2000000000000 : ℚ) : ℝ) ≤ stT211 158 := by
  have hc : ((126537/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100667396109/2000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((126537/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c159 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((180477/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1113811/10000000) (δ := 10681/1000000000) (ψ := 95177/100000) 211 170
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t159 : ((143119534817/2000000000000 : ℚ) : ℝ) ≤ stT211 159 := by
  have hc : ((180467/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143119534817/2000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((180467/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c160 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-19633/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 176841/400000) (δ := 10681/1000000000) (ψ := 95177/100000) 211 170
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t160 : ((-776260683/50000000000 : ℚ) : ℝ) ≤ stT211 160 := by
  have hc : ((-9819/50000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-776260683/50000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-9819/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c161 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-998287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3853807/5000000) (δ := 10581/1000000000) (ψ := 95177/100000) 211 170
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t161 : ((-786800371407/10000000000000 : ℚ) : ℝ) ≤ stT211 161 := by
  have hc : ((-998337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-786800371407/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-998337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c162 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-317253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4734069/10000000) (δ := 10629/1000000000) (ψ := 95177/100000) 211 171
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t162 : ((-9971881381/400000000000 : ℚ) : ℝ) ≤ stT211 162 := by
  have hc : ((-317303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9971881381/400000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-317303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c163 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((414031/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1487887/10000000) (δ := 5287/500000000) (ψ := 95177/100000) 211 171
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t163 : ((8106858489/125000000000 : ℚ) : ℝ) ≤ stT211 163 := by
  have hc : ((207003/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8106858489/125000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((207003/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c164 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((767821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1738409/10000000) (δ := 10729/1000000000) (ψ := 95177/100000) 211 171
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t164 : ((149881951307/2500000000000 : ℚ) : ℝ) ≤ stT211 164 := by
  have hc : ((767771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149881951307/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((767771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c165 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-396073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4945081/10000000) (δ := 5287/500000000) (ψ := 95177/100000) 211 171
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t165 : ((-308381359377/10000000000000 : ℚ) : ℝ) ≤ stT211 165 := by
  have hc : ((-396123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-308381359377/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-396123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c166 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-198761/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7575569/10000000) (δ := 10567/1000000000) (ψ := 95177/100000) 211 172
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t166 : ((-154276310421/2000000000000 : ℚ) : ℝ) ≤ stT211 166 := by
  have hc : ((-198771/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154276310421/2000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-198771/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c167 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-47741/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4407351/10000000) (δ := 2659/250000000) (ψ := 95177/100000) 211 172
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t167 : ((-1154775137/78125000000 : ℚ) : ℝ) ≤ stT211 167 := by
  have hc : ((-95507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1154775137/78125000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-95507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c168 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((43801/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1258123/10000000) (δ := 671/62500000) (ψ := 95177/100000) 211 172
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t168 : ((16895621763/250000000000 : ℚ) : ℝ) ≤ stT211 168 := by
  have hc : ((87597/100000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16895621763/250000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((87597/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c169 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((366187/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 468121/2500000) (δ := 671/62500000) (ψ := 95177/100000) 211 172
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t169 : ((14083139763/250000000000 : ℚ) : ℝ) ≤ stT211 169 := by
  have hc : ((183081/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14083139763/250000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((183081/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c170 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-410529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 199383/400000) (δ := 10667/1000000000) (ψ := 95177/100000) 211 172
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t170 : ((-62979944547/2000000000000 : ℚ) : ℝ) ≤ stT211 170 := by
  have hc : ((-410579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62979944547/2000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-410579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c171 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-995973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1907387/2500000) (δ := 10659/1000000000) (ψ := 95177/100000) 211 173
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t171 : ((-9520983857/125000000000 : ℚ) : ℝ) ≤ stT211 171 := by
  have hc : ((-996023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9520983857/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-996023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c172 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-49617/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1138437/2500000) (δ := 10559/1000000000) (ψ := 95177/100000) 211 173
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t172 : ((-37840240111/2000000000000 : ℚ) : ℝ) ≤ stT211 172 := by
  have hc : ((-49627/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37840240111/2000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-49627/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c173 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((51643/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -747889/5000000) (δ := 10659/1000000000) (ψ := 95177/100000) 211 173
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t173 : ((62817635783/1000000000000 : ℚ) : ℝ) ≤ stT211 173 := by
  have hc : ((413119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62817635783/1000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((413119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c174 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((407569/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 772287/5000000) (δ := 10559/1000000000) (ψ := 95177/100000) 211 173
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t174 : ((19309893207/312500000000 : ℚ) : ℝ) ≤ stT211 174 := by
  have hc : ((50943/62500 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19309893207/312500000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((50943/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c175 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-253417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2283759/5000000) (δ := 10659/1000000000) (ψ := 95177/100000) 211 173
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t175 : ((-191603055843/10000000000000 : ℚ) : ℝ) ≤ stT211 175 := by
  have hc : ((-253467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191603055843/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-253467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c176 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-9937/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7573213/10000000) (δ := 10659/1000000000) (ψ := 95177/100000) 211 173
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t176 : ((-119850861/1600000000 : ℚ) : ℝ) ≤ stT211 176 := by
  have hc : ((-159/160 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119850861/1600000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-159/160 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c177 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-117131/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -128651/250000) (δ := 10751/1000000000) (ψ := 95177/100000) 211 174
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t177 : ((-176101120689/5000000000000 : ℚ) : ℝ) ≤ stT211 177 := by
  have hc : ((-234287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176101120689/5000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-234287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c178 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((161267/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2174211/10000000) (δ := 1319/125000000) (ψ := 95177/100000) 211 174
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t178 : ((241730493279/5000000000000 : ℚ) : ℝ) ≤ stT211 178 := by
  have hc : ((322509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((241730493279/5000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((322509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c179 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((475799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 390501/5000000) (δ := 2663/250000000) (ψ := 95177/100000) 211 174
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t179 : ((35561013969/500000000000 : ℚ) : ℝ) ≤ stT211 179 := by
  have hc : ((237887/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35561013969/500000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((237887/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c180 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((82819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 743941/2000000) (δ := 10651/1000000000) (ψ := 95177/100000) 211 174
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t180 : ((12338457599/2000000000000 : ℚ) : ℝ) ≤ stT211 180 := by
  have hc : ((82769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12338457599/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((82769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c181 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-884801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 83027/125000) (δ := 2663/250000000) (ψ := 95177/100000) 211 174
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t181 : ((-131541064809/2000000000000 : ℚ) : ℝ) ≤ stT211 181 := by
  have hc : ((-884851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131541064809/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-884851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c182 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-194739/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6159489/10000000) (δ := 5279/500000000) (ψ := 95177/100000) 211 175
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t182 : ((-230975279/4000000000 : ℚ) : ℝ) ≤ stT211 182 := by
  have hc : ((-389503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230975279/4000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-389503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c183 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((65037/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3269053/10000000) (δ := 2129/200000000) (ψ := 95177/100000) 211 175
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t183 : ((96134951829/5000000000000 : ℚ) : ℝ) ≤ stT211 183 := by
  have hc : ((130049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96134951829/5000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((130049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c184 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((493791/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -394389/10000000) (δ := 2129/200000000) (ψ := 95177/100000) 211 175
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t184 : ((182004369547/2500000000000 : ℚ) : ℝ) ≤ stT211 184 := by
  have hc : ((246883/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182004369547/2500000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((246883/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c185 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((4417/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1232357/5000000) (δ := 5279/500000000) (ψ := 95177/100000) 211 175
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t185 : ((8117865381/200000000000 : ℚ) : ℝ) ≤ stT211 185 := by
  have hc : ((22083/40000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8117865381/200000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((22083/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c186 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-262429/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5308361/10000000) (δ := 5279/500000000) (ψ := 95177/100000) 211 175
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t186 : ((-24055090143/625000000000 : ℚ) : ℝ) ≤ stT211 186 := by
  have hc : ((-131227/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24055090143/625000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-131227/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c187 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-993607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7571147/10000000) (δ := 2133/200000000) (ψ := 95177/100000) 211 176
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t187 : ((-726634535361/10000000000000 : ℚ) : ℝ) ≤ stT211 187 := by
  have hc : ((-993657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-726634535361/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-993657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c188 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-326253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -594729/1250000) (δ := 5369/500000000) (ψ := 95177/100000) 211 176
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t188 : ((-9519237419/400000000000 : ℚ) : ℝ) ≤ stT211 188 := by
  have hc : ((-326303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9519237419/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-326303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c189 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((708267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1959391/10000000) (δ := 2133/200000000) (ψ := 95177/100000) 211 176
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t189 : ((16098480627/312500000000 : ℚ) : ℝ) ≤ stT211 189 := by
  have hc : ((708217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16098480627/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((708217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c190 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((946143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 412113/5000000) (δ := 5319/500000000) (ψ := 95177/100000) 211 176
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t190 : ((171591941317/2500000000000 : ℚ) : ℝ) ≤ stT211 190 := by
  have hc : ((946093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171591941317/2500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((946093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c191 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((66543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 718657/2000000) (δ := 2133/200000000) (ψ := 95177/100000) 211 176
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t191 : ((12032673833/1250000000000 : ℚ) : ℝ) ≤ stT211 191 := by
  have hc : ((33259/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12032673833/1250000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((33259/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c192 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-164789/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6347837/10000000) (δ := 2113/200000000) (ψ := 95177/100000) 211 176
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t192 : ((-14866682589/250000000000 : ℚ) : ℝ) ≤ stT211 192 := by
  have hc : ((-164799/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14866682589/250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-164799/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c193 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-220153/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6619869/10000000) (δ := 667/62500000) (ψ := 95177/100000) 211 177
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t193 : ((-39619662387/625000000000 : ℚ) : ℝ) ≤ stT211 193 := by
  have hc : ((-440331/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39619662387/625000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-440331/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c194 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((831/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3893749/10000000) (δ := 667/62500000) (ψ := 95177/100000) 211 177
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t194 : ((2377517917/2500000000000 : ℚ) : ℝ) ≤ stT211 194 := by
  have hc : ((6623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2377517917/2500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((6623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c195 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((445179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1181661/10000000) (δ := 10631/1000000000) (ψ := 95177/100000) 211 177
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t195 : ((79695252889/1250000000000 : ℚ) : ℝ) ≤ stT211 195 := by
  have hc : ((222577/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79695252889/1250000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((222577/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c196 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((821579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 758277/5000000) (δ := 10731/1000000000) (ψ := 95177/100000) 211 177
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t196 : ((117361168353/2000000000000 : ℚ) : ℝ) ≤ stT211 196 := by
  have hc : ((821529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117361168353/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((821529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c197 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-54703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 840211/2000000) (δ := 667/62500000) (ψ := 95177/100000) 211 177
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t197 : ((-4874014111/625000000000 : ℚ) : ℝ) ≤ stT211 197 := by
  have hc : ((-6841/62500 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4874014111/625000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-6841/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c198 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-184767/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1374389/2000000) (δ := 10731/1000000000) (ψ := 95177/100000) 211 177
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t198 : ((-13131547059/200000000000 : ℚ) : ℝ) ≤ stT211 198 := by
  have hc : ((-184777/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13131547059/200000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-184777/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c199 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-783721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3089289/5000000) (δ := 10679/1000000000) (ψ := 95177/100000) 211 178
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t199 : ((-277800577011/5000000000000 : ℚ) : ℝ) ≤ stT211 199 := by
  have hc : ((-783771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277800577011/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-783771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c200 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((78179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -706897/2000000) (δ := 2681/250000000) (ψ := 95177/100000) 211 178
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t200 : ((13815790581/1250000000000 : ℚ) : ℝ) ≤ stT211 200 := by
  have hc : ((39077/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13815790581/1250000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((39077/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c201 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((935399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -451763/5000000) (δ := 2681/250000000) (ψ := 95177/100000) 211 178
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t201 : ((131948748081/2000000000000 : ℚ) : ℝ) ≤ stT211 201 := by
  have hc : ((935349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131948748081/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((935349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c202 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((193491/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1714299/10000000) (δ := 10679/1000000000) (ψ := 95177/100000) 211 178
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t202 : ((272261784329/5000000000000 : ℚ) : ℝ) ≤ stT211 202 := by
  have hc : ((386957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272261784329/5000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((386957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c203 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-156261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1079813/2500000) (δ := 10579/1000000000) (ψ := 95177/100000) 211 178
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t203 : ((-109708907393/10000000000000 : ℚ) : ℝ) ≤ stT211 203 := by
  have hc : ((-156311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109708907393/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-156311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c204 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-929759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6911387/10000000) (δ := 10579/1000000000) (ψ := 95177/100000) 211 178
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t204 : ((-650997403069/10000000000000 : ℚ) : ℝ) ≤ stT211 204 := by
  have hc : ((-929809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-650997403069/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-929809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c205 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-793199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6217101/10000000) (δ := 10687/1000000000) (ψ := 95177/100000) 211 179
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t205 : ((-554029692319/10000000000000 : ℚ) : ℝ) ≤ stT211 205 := by
  have hc : ((-793249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-554029692319/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-793249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c206 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((55249/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3650181/10000000) (δ := 1327/125000000) (ψ := 95177/100000) 211 179
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t206 : ((4809547899/625000000000 : ℚ) : ℝ) ≤ stT211 206 := by
  have hc : ((6903/62500 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4809547899/625000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((6903/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c207 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((905481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1095709/10000000) (δ := 10687/1000000000) (ψ := 95177/100000) 211 179
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t207 : ((78664750711/1250000000000 : ℚ) : ℝ) ≤ stT211 207 := by
  have hc : ((905431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78664750711/1250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((905431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c208 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((167447/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1446471/10000000) (δ := 2679/250000000) (ψ := 95177/100000) 211 179
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t208 : ((928773039/16000000000 : ℚ) : ℝ) ≤ stT211 208 := by
  have hc : ((167437/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((928773039/16000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((167437/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c209 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-19789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3976467/10000000) (δ := 10587/1000000000) (ψ := 95177/100000) 211 179
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t209 : ((-2744586777/2000000000000 : ℚ) : ℝ) ≤ stT211 209 := by
  have hc : ((-19839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2744586777/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-19839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c210 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-53483/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6494383/10000000) (δ := 10687/1000000000) (ψ := 95177/100000) 211 179
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t210 : ((-147635825337/2500000000000 : ℚ) : ℝ) ≤ stT211 210 := by
  have hc : ((-427889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147635825337/2500000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-427889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c211 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-896701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6707639/10000000) (δ := 5297/500000000) (ψ := 95177/100000) 211 180
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t211 : ((-617349394179/10000000000000 : ℚ) : ℝ) ≤ stT211 211 := by
  have hc : ((-896751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-617349394179/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-896751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c212 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-114379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2106783/5000000) (δ := 5347/500000000) (ψ := 95177/100000) 211 180
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t212 : ((-78590180487/10000000000000 : ℚ) : ℝ) ≤ stT211 212 := by
  have hc : ((-114429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78590180487/10000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-114429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c213 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((12026/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -432801/2500000) (δ := 5297/500000000) (ψ := 95177/100000) 211 180
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t213 : ((65916284679/1250000000000 : ℚ) : ℝ) ≤ stT211 213 := by
  have hc : ((384807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65916284679/1250000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((384807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c214 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((956563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 739553/10000000) (δ := 10609/1000000000) (ψ := 95177/100000) 211 180
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t214 : ((130771587821/2000000000000 : ℚ) : ℝ) ≤ stT211 214 := by
  have hc : ((956513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130771587821/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((956513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c215 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((287191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1599379/5000000) (δ := 10609/1000000000) (ψ := 95177/100000) 211 180
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t215 : ((97914219577/5000000000000 : ℚ) : ℝ) ≤ stT211 215 := by
  have hc : ((287141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97914219577/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((287141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c216 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-634863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5646569/10000000) (δ := 10609/1000000000) (ψ := 95177/100000) 211 180
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t216 : ((-216001846991/5000000000000 : ℚ) : ℝ) ≤ stT211 216 := by
  have hc : ((-634913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-216001846991/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-634913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c217 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-497903/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1906231/2500000) (δ := 10701/1000000000) (ψ := 95177/100000) 211 181
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t217 : ((-8450398329/125000000000 : ℚ) : ℝ) ≤ stT211 217 := by
  have hc : ((-62241/62500 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8450398329/125000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-62241/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c218 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-121839/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2599819/5000000) (δ := 5351/500000000) (ψ := 95177/100000) 211 181
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t218 : ((-82528315029/2500000000000 : ℚ) : ℝ) ≤ stT211 218 := by
  have hc : ((-243703/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82528315029/2500000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-243703/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c219 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((220461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -696357/2500000) (δ := 10701/1000000000) (ψ := 95177/100000) 211 181
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t219 : ((37239190333/1250000000000 : ℚ) : ℝ) ≤ stT211 219 := by
  have hc : ((55109/125000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37239190333/1250000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((55109/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c220 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((494167/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -95561/2500000) (δ := 5301/500000000) (ψ := 95177/100000) 211 181
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t220 : ((166575021129/2500000000000 : ℚ) : ℝ) ≤ stT211 220 := by
  have hc : ((247071/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166575021129/2500000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((247071/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c221 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((69381/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1005037/5000000) (δ := 5301/500000000) (ψ := 95177/100000) 211 181
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t221 : ((11393382/244140625 : ℚ) : ℝ) ≤ stT211 221 := by
  have hc : ((2168/3125 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11393382/244140625 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((2168/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c222 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-184747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2195763/5000000) (δ := 10701/1000000000) (ψ := 95177/100000) 211 181
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t222 : ((-124027800129/10000000000000 : ℚ) : ℝ) ≤ stT211 222 := by
  have hc : ((-184797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124027800129/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-184797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c223 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-113271/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3381161/5000000) (δ := 10701/1000000000) (ψ := 95177/100000) 211 181
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t223 : ((-6068488837/100000000000 : ℚ) : ℝ) ≤ stT211 223 := by
  have hc : ((-453109/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6068488837/100000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-453109/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c224 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-218501/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -823181/1250000) (δ := 2677/250000000) (ψ := 95177/100000) 211 182
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t224 : ((-146000669079/2500000000000 : ℚ) : ℝ) ≤ stT211 224 := by
  have hc : ((-437027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146000669079/2500000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-437027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c225 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-123191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -529469/1250000) (δ := 2677/250000000) (ψ := 95177/100000) 211 182
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t225 : ((-82160707747/10000000000000 : ℚ) : ℝ) ≤ stT211 225 := by
  have hc : ((-123241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82160707747/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-123241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c226 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((22681/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1896527/10000000) (δ := 2651/125000000) (ψ := 95177/100000) 211 182
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t226 : ((24137816049/500000000000 : ℚ) : ℝ) ≤ stT211 226 := by
  have hc : ((362871/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24137816049/500000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((362871/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c227 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((985079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 108103/2500000) (δ := 2677/250000000) (ψ := 95177/100000) 211 182
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t227 : ((653786402967/10000000000000 : ℚ) : ℝ) ≤ stT211 227 := by
  have hc : ((985029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((653786402967/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((985029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c228 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((453207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2751091/10000000) (δ := 2677/250000000) (ψ := 95177/100000) 211 182
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t228 : ((150055236881/5000000000000 : ℚ) : ℝ) ≤ stT211 228 := by
  have hc : ((453157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150055236881/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((453157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c229 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-437719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2529821/5000000) (δ := 2677/250000000) (ψ := 95177/100000) 211 182
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t229 : ((-289286072811/10000000000000 : ℚ) : ℝ) ≤ stT211 229 := by
  have hc : ((-437769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-289286072811/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-437769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c230 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-490197/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7358117/10000000) (δ := 2139/200000000) (ψ := 95177/100000) 211 182
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t230 : ((-161621536291/2500000000000 : ℚ) : ℝ) ≤ stT211 230 := by
  have hc : ((-245111/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161621536291/2500000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-245111/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c231 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-753743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -303067/500000) (δ := 2647/250000000) (ψ := 95177/100000) 211 183
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t231 : ((-15498737873/312500000000 : ℚ) : ℝ) ≤ stT211 231 := by
  have hc : ((-753793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15498737873/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-753793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c232 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((901/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3782751/10000000) (δ := 2647/250000000) (ψ := 95177/100000) 211 183
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t232 : ((4728179331/1250000000000 : ℚ) : ℝ) ≤ stT211 232 := by
  have hc : ((28807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4728179331/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((28807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c233 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((822179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1513921/10000000) (δ := 167/15625000) (ψ := 95177/100000) 211 183
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t233 : ((538593972609/10000000000000 : ℚ) : ℝ) ≤ stT211 233 := by
  have hc : ((822129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((538593972609/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((822129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c234 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((477951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 186301/2500000) (δ := 2143/200000000) (ψ := 95177/100000) 211 183
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t234 : ((3905372309/62500000000 : ℚ) : ℝ) ≤ stT211 234 := by
  have hc : ((238963/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3905372309/62500000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((238963/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c235 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((182171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119787/400000) (δ := 2143/200000000) (ψ := 95177/100000) 211 183
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t235 : ((7426183493/312500000000 : ℚ) : ℝ) ≤ stT211 235 := by
  have hc : ((91073/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7426183493/312500000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((91073/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c236 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-249759/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2617299/5000000) (δ := 2123/200000000) (ψ := 95177/100000) 211 183
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t236 : ((-4064891147/125000000000 : ℚ) : ℝ) ≤ stT211 236 := by
  have hc : ((-31223/62500 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4064891147/125000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-31223/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c237 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-987921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3732513/5000000) (δ := 2647/250000000) (ψ := 95177/100000) 211 183
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t237 : ((-64175632247/1000000000000 : ℚ) : ℝ) ≤ stT211 237 := by
  have hc : ((-987971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64175632247/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-987971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c238 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-371641/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3010949/5000000) (δ := 10723/1000000000) (ψ := 95177/100000) 211 184
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t238 : ((-30114423483/625000000000 : ℚ) : ℝ) ≤ stT211 238 := by
  have hc : ((-185833/250000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30114423483/625000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-185833/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c239 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((23361/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -119067/312500) (δ := 267/25000000) (ψ := 95177/100000) 211 184
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t239 : ((943424891/312500000000 : ℚ) : ℝ) ≤ stT211 239 := by
  have hc : ((2917/62500 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((943424891/312500000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((2917/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c240 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((50017/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -80381/500000) (δ := 10623/1000000000) (ψ := 95177/100000) 211 184
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t240 : ((258270450167/5000000000000 : ℚ) : ℝ) ≤ stT211 240 := by
  have hc : ((400111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258270450167/5000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((400111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c241 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((972679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23429/400000) (δ := 10623/1000000000) (ψ := 95177/100000) 211 184
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t241 : ((156631201531/2500000000000 : ℚ) : ℝ) ≤ stT211 241 := by
  have hc : ((972629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156631201531/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((972629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c242 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((446453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2769997/10000000) (δ := 10623/1000000000) (ψ := 95177/100000) 211 184
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t242 : ((35869820259/1250000000000 : ℚ) : ℝ) ≤ stT211 242 := by
  have hc : ((446403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35869820259/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((446403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c243 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-79227/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4945249/10000000) (δ := 10723/1000000000) (ψ := 95177/100000) 211 184
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t243 : ((-50830614737/2000000000000 : ℚ) : ℝ) ≤ stT211 243 := by
  have hc : ((-79237/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50830614737/2000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-79237/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c244 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-956231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3555793/5000000) (δ := 10723/1000000000) (ψ := 95177/100000) 211 184
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t244 : ((-122439350397/2000000000000 : ℚ) : ℝ) ≤ stT211 244 := by
  have hc : ((-956281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122439350397/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-956281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c245 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-844041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6438929/10000000) (δ := 2113/100000000) (ψ := 95177/100000) 211 185
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t245 : ((-539270325807/10000000000000 : ℚ) : ℝ) ≤ stT211 245 := by
  have hc : ((-844091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-539270325807/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-844091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c246 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-36197/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4290237/10000000) (δ := 10573/1000000000) (ψ := 95177/100000) 211 185
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t246 : ((-46172688763/5000000000000 : ℚ) : ℝ) ≤ stT211 246 := by
  have hc : ((-72419/500000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46172688763/5000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-72419/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c247 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((326177/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -86011/400000) (δ := 10573/1000000000) (ψ := 95177/100000) 211 185
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t247 : ((6485165599/156250000000 : ℚ) : ℝ) ≤ stT211 247 := by
  have hc : ((40769/62500 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6485165599/156250000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((40769/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c248 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((999971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4741/2500000) (δ := 10573/1000000000) (ψ := 95177/100000) 211 185
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t248 : ((126989967/2000000000 : ℚ) : ℝ) ≤ stT211 248 := by
  have hc : ((999921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126989967/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((999921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c249 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((133269/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2103749/10000000) (δ := 1063/100000000) (ψ := 95177/100000) 211 185
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t249 : ((21112356629/500000000000 : ℚ) : ℝ) ≤ stT211 249 := by
  have hc : ((133259/200000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21112356629/500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((133259/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_c250 :
    |Real.cos (((211 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((-2323/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2109011/5000000) (δ := 1073/100000000) (ψ := 95177/100000) 211 185
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st211_t250 : ((-45932117/6250000000 : ℚ) : ℝ) ≤ stT211 250 := by
  have hc : ((-581/5000 : ℚ) : ℝ)
      ≤ Real.cos (((211 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((95177/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st211_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45932117/6250000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-581/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st211_p1 : ((18131/31250 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT211 (i+1) := by
  rw [Finset.sum_range_one]
  exact st211_t1

theorem st211_p2 : ((5391722137549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT211 (i+1))
      = (∑ i ∈ Finset.range 1, stT211 (i+1)) + stT211 2 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 1
    simpa using h
  have hprev := st211_p1
  have hstep := st211_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p3 : ((5242557914041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT211 (i+1))
      = (∑ i ∈ Finset.range 2, stT211 (i+1)) + stT211 3 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 2
    simpa using h
  have hprev := st211_p2
  have hstep := st211_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p4 : ((1597931252351/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT211 (i+1))
      = (∑ i ∈ Finset.range 3, stT211 (i+1)) + stT211 4 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 3
    simpa using h
  have hprev := st211_p3
  have hstep := st211_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p5 : ((4972637268067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT211 (i+1))
      = (∑ i ∈ Finset.range 4, stT211 (i+1)) + stT211 5 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 4
    simpa using h
  have hprev := st211_p4
  have hstep := st211_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p6 : ((6999495683981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT211 (i+1))
      = (∑ i ∈ Finset.range 5, stT211 (i+1)) + stT211 6 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 5
    simpa using h
  have hprev := st211_p5
  have hstep := st211_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p7 : ((7634207521257/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT211 (i+1))
      = (∑ i ∈ Finset.range 6, stT211 (i+1)) + stT211 7 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 6
    simpa using h
  have hprev := st211_p6
  have hstep := st211_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p8 : ((6878313887591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT211 (i+1))
      = (∑ i ∈ Finset.range 7, stT211 (i+1)) + stT211 8 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 7
    simpa using h
  have hprev := st211_p7
  have hstep := st211_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p9 : ((2888184333601/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT211 (i+1))
      = (∑ i ∈ Finset.range 8, stT211 (i+1)) + stT211 9 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 8
    simpa using h
  have hprev := st211_p8
  have hstep := st211_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p10 : ((13019550034023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT211 (i+1))
      = (∑ i ∈ Finset.range 9, stT211 (i+1)) + stT211 10 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 9
    simpa using h
  have hprev := st211_p9
  have hstep := st211_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p11 : ((2180426994117/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT211 (i+1))
      = (∑ i ∈ Finset.range 10, stT211 (i+1)) + stT211 11 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 10
    simpa using h
  have hprev := st211_p10
  have hstep := st211_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p12 : ((10081064759481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT211 (i+1))
      = (∑ i ∈ Finset.range 11, stT211 (i+1)) + stT211 12 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 11
    simpa using h
  have hprev := st211_p11
  have hstep := st211_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p13 : ((12840181388481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT211 (i+1))
      = (∑ i ∈ Finset.range 12, stT211 (i+1)) + stT211 13 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 12
    simpa using h
  have hprev := st211_p12
  have hstep := st211_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p14 : ((31897284621/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT211 (i+1))
      = (∑ i ∈ Finset.range 13, stT211 (i+1)) + stT211 14 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 13
    simpa using h
  have hprev := st211_p13
  have hstep := st211_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p15 : ((2710051533613/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT211 (i+1))
      = (∑ i ∈ Finset.range 14, stT211 (i+1)) + stT211 15 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 14
    simpa using h
  have hprev := st211_p14
  have hstep := st211_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p16 : ((3312079658613/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT211 (i+1))
      = (∑ i ∈ Finset.range 15, stT211 (i+1)) + stT211 16 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 15
    simpa using h
  have hprev := st211_p15
  have hstep := st211_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p17 : ((3917737133577/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT211 (i+1))
      = (∑ i ∈ Finset.range 16, stT211 (i+1)) + stT211 17 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 16
    simpa using h
  have hprev := st211_p16
  have hstep := st211_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p18 : ((8838701790591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT211 (i+1))
      = (∑ i ∈ Finset.range 17, stT211 (i+1)) + stT211 18 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 17
    simpa using h
  have hprev := st211_p17
  have hstep := st211_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p19 : ((1084864640891/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT211 (i+1))
      = (∑ i ∈ Finset.range 18, stT211 (i+1)) + stT211 19 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 18
    simpa using h
  have hprev := st211_p18
  have hstep := st211_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p20 : ((95186722937/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT211 (i+1))
      = (∑ i ∈ Finset.range 19, stT211 (i+1)) + stT211 20 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 19
    simpa using h
  have hprev := st211_p19
  have hstep := st211_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p21 : ((133448788861/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT211 (i+1))
      = (∑ i ∈ Finset.range 20, stT211 (i+1)) + stT211 21 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 20
    simpa using h
  have hprev := st211_p20
  have hstep := st211_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p22 : ((197982492983/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT211 (i+1))
      = (∑ i ∈ Finset.range 21, stT211 (i+1)) + stT211 22 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 21
    simpa using h
  have hprev := st211_p21
  have hstep := st211_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p23 : ((214120464971/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT211 (i+1))
      = (∑ i ∈ Finset.range 22, stT211 (i+1)) + stT211 23 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 22
    simpa using h
  have hprev := st211_p22
  have hstep := st211_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p24 : ((7649494046789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT211 (i+1))
      = (∑ i ∈ Finset.range 23, stT211 (i+1)) + stT211 24 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 23
    simpa using h
  have hprev := st211_p23
  have hstep := st211_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p25 : ((8587791046789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT211 (i+1))
      = (∑ i ∈ Finset.range 24, stT211 (i+1)) + stT211 25 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 24
    simpa using h
  have hprev := st211_p24
  have hstep := st211_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p26 : ((4260260124223/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT211 (i+1))
      = (∑ i ∈ Finset.range 25, stT211 (i+1)) + stT211 26 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 25
    simpa using h
  have hprev := st211_p25
  have hstep := st211_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p27 : ((3786698163153/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT211 (i+1))
      = (∑ i ∈ Finset.range 26, stT211 (i+1)) + stT211 27 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 26
    simpa using h
  have hprev := st211_p26
  have hstep := st211_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p28 : ((7570922547999/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT211 (i+1))
      = (∑ i ∈ Finset.range 27, stT211 (i+1)) + stT211 28 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 27
    simpa using h
  have hprev := st211_p27
  have hstep := st211_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p29 : ((16811990481151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT211 (i+1))
      = (∑ i ∈ Finset.range 28, stT211 (i+1)) + stT211 29 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 28
    simpa using h
  have hprev := st211_p28
  have hstep := st211_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p30 : ((18480637422547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT211 (i+1))
      = (∑ i ∈ Finset.range 29, stT211 (i+1)) + stT211 30 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 29
    simpa using h
  have hprev := st211_p29
  have hstep := st211_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p31 : ((4842293843637/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT211 (i+1))
      = (∑ i ∈ Finset.range 30, stT211 (i+1)) + stT211 31 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 30
    simpa using h
  have hprev := st211_p30
  have hstep := st211_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p32 : ((9774346889807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT211 (i+1))
      = (∑ i ∈ Finset.range 31, stT211 (i+1)) + stT211 32 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 31
    simpa using h
  have hprev := st211_p31
  have hstep := st211_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p33 : ((3872246945363/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT211 (i+1))
      = (∑ i ∈ Finset.range 32, stT211 (i+1)) + stT211 33 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 32
    simpa using h
  have hprev := st211_p32
  have hstep := st211_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p34 : ((19149641469121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT211 (i+1))
      = (∑ i ∈ Finset.range 33, stT211 (i+1)) + stT211 34 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 33
    simpa using h
  have hprev := st211_p33
  have hstep := st211_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p35 : ((19222520788849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT211 (i+1))
      = (∑ i ∈ Finset.range 34, stT211 (i+1)) + stT211 35 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 34
    simpa using h
  have hprev := st211_p34
  have hstep := st211_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p36 : ((19844203873509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT211 (i+1))
      = (∑ i ∈ Finset.range 35, stT211 (i+1)) + stT211 36 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 35
    simpa using h
  have hprev := st211_p35
  have hstep := st211_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p37 : ((21115701133867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT211 (i+1))
      = (∑ i ∈ Finset.range 36, stT211 (i+1)) + stT211 37 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 36
    simpa using h
  have hprev := st211_p36
  have hstep := st211_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p38 : ((22737089426941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT211 (i+1))
      = (∑ i ∈ Finset.range 37, stT211 (i+1)) + stT211 38 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 37
    simpa using h
  have hprev := st211_p37
  have hstep := st211_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p39 : ((2388429357249/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT211 (i+1))
      = (∑ i ∈ Finset.range 38, stT211 (i+1)) + stT211 39 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 38
    simpa using h
  have hprev := st211_p38
  have hstep := st211_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p40 : ((23659839823467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT211 (i+1))
      = (∑ i ∈ Finset.range 39, stT211 (i+1)) + stT211 40 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 39
    simpa using h
  have hprev := st211_p39
  have hstep := st211_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p41 : ((22195599565069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT211 (i+1))
      = (∑ i ∈ Finset.range 40, stT211 (i+1)) + stT211 41 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 40
    simpa using h
  have hprev := st211_p40
  have hstep := st211_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p42 : ((21169321479533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT211 (i+1))
      = (∑ i ∈ Finset.range 41, stT211 (i+1)) + stT211 42 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 41
    simpa using h
  have hprev := st211_p41
  have hstep := st211_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p43 : ((5504638400337/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT211 (i+1))
      = (∑ i ∈ Finset.range 42, stT211 (i+1)) + stT211 43 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 42
    simpa using h
  have hprev := st211_p42
  have hstep := st211_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p44 : ((5843612366937/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT211 (i+1))
      = (∑ i ∈ Finset.range 43, stT211 (i+1)) + stT211 44 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 43
    simpa using h
  have hprev := st211_p43
  have hstep := st211_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p45 : ((5690638855599/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT211 (i+1))
      = (∑ i ∈ Finset.range 44, stT211 (i+1)) + stT211 45 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 44
    simpa using h
  have hprev := st211_p44
  have hstep := st211_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p46 : ((5366743430469/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT211 (i+1))
      = (∑ i ∈ Finset.range 45, stT211 (i+1)) + stT211 46 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 45
    simpa using h
  have hprev := st211_p45
  have hstep := st211_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p47 : ((11187673693313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT211 (i+1))
      = (∑ i ∈ Finset.range 46, stT211 (i+1)) + stT211 47 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 46
    simpa using h
  have hprev := st211_p46
  have hstep := st211_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p48 : ((23223715580251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT211 (i+1))
      = (∑ i ∈ Finset.range 47, stT211 (i+1)) + stT211 48 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 47
    simpa using h
  have hprev := st211_p47
  have hstep := st211_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p49 : ((21845547886127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT211 (i+1))
      = (∑ i ∈ Finset.range 48, stT211 (i+1)) + stT211 49 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 48
    simpa using h
  have hprev := st211_p48
  have hstep := st211_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p50 : ((2762850744843/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT211 (i+1))
      = (∑ i ∈ Finset.range 49, stT211 (i+1)) + stT211 50 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 49
    simpa using h
  have hprev := st211_p49
  have hstep := st211_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p51 : ((2894777774973/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT211 (i+1))
      = (∑ i ∈ Finset.range 50, stT211 (i+1)) + stT211 51 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 50
    simpa using h
  have hprev := st211_p50
  have hstep := st211_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p52 : ((10905345645783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT211 (i+1))
      = (∑ i ∈ Finset.range 51, stT211 (i+1)) + stT211 52 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 51
    simpa using h
  have hprev := st211_p51
  have hstep := st211_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p53 : ((22413790423681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT211 (i+1))
      = (∑ i ∈ Finset.range 52, stT211 (i+1)) + stT211 53 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 52
    simpa using h
  have hprev := st211_p52
  have hstep := st211_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p54 : ((22877571151897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT211 (i+1))
      = (∑ i ∈ Finset.range 53, stT211 (i+1)) + stT211 54 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 53
    simpa using h
  have hprev := st211_p53
  have hstep := st211_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p55 : ((21689610525897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT211 (i+1))
      = (∑ i ∈ Finset.range 54, stT211 (i+1)) + stT211 55 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 54
    simpa using h
  have hprev := st211_p54
  have hstep := st211_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p56 : ((23007166816411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT211 (i+1))
      = (∑ i ∈ Finset.range 55, stT211 (i+1)) + stT211 56 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 55
    simpa using h
  have hprev := st211_p55
  have hstep := st211_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p57 : ((1102371371177/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT211 (i+1))
      = (∑ i ∈ Finset.range 56, stT211 (i+1)) + stT211 57 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 56
    simpa using h
  have hprev := st211_p56
  have hstep := st211_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p58 : ((5603279265151/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT211 (i+1))
      = (∑ i ∈ Finset.range 57, stT211 (i+1)) + stT211 58 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 57
    simpa using h
  have hprev := st211_p57
  have hstep := st211_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p59 : ((22650023103823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT211 (i+1))
      = (∑ i ∈ Finset.range 58, stT211 (i+1)) + stT211 59 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 58
    simpa using h
  have hprev := st211_p58
  have hstep := st211_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p60 : ((5483529652377/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT211 (i+1))
      = (∑ i ∈ Finset.range 59, stT211 (i+1)) + stT211 60 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 59
    simpa using h
  have hprev := st211_p59
  have hstep := st211_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p61 : ((5740838167313/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT211 (i+1))
      = (∑ i ∈ Finset.range 60, stT211 (i+1)) + stT211 61 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 60
    simpa using h
  have hprev := st211_p60
  have hstep := st211_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p62 : ((10884618549379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT211 (i+1))
      = (∑ i ∈ Finset.range 61, stT211 (i+1)) + stT211 62 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 61
    simpa using h
  have hprev := st211_p61
  have hstep := st211_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p63 : ((287762587311/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT211 (i+1))
      = (∑ i ∈ Finset.range 62, stT211 (i+1)) + stT211 63 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 62
    simpa using h
  have hprev := st211_p62
  have hstep := st211_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p64 : ((4354769947431/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT211 (i+1))
      = (∑ i ∈ Finset.range 63, stT211 (i+1)) + stT211 64 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 63
    simpa using h
  have hprev := st211_p63
  have hstep := st211_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p65 : ((11494951030233/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT211 (i+1))
      = (∑ i ∈ Finset.range 64, stT211 (i+1)) + stT211 65 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 64
    simpa using h
  have hprev := st211_p64
  have hstep := st211_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p66 : ((5451533391699/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT211 (i+1))
      = (∑ i ∈ Finset.range 65, stT211 (i+1)) + stT211 66 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 65
    simpa using h
  have hprev := st211_p65
  have hstep := st211_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p67 : ((5742452940531/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT211 (i+1))
      = (∑ i ∈ Finset.range 66, stT211 (i+1)) + stT211 67 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 66
    simpa using h
  have hprev := st211_p66
  have hstep := st211_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p68 : ((21808980852769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT211 (i+1))
      = (∑ i ∈ Finset.range 67, stT211 (i+1)) + stT211 68 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 67
    simpa using h
  have hprev := st211_p67
  have hstep := st211_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p69 : ((4596083069051/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT211 (i+1))
      = (∑ i ∈ Finset.range 68, stT211 (i+1)) + stT211 69 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 68
    simpa using h
  have hprev := st211_p68
  have hstep := st211_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p70 : ((85135646359/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT211 (i+1))
      = (∑ i ∈ Finset.range 69, stT211 (i+1)) + stT211 70 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 69
    simpa using h
  have hprev := st211_p69
  have hstep := st211_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p71 : ((718161396093/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT211 (i+1))
      = (∑ i ∈ Finset.range 70, stT211 (i+1)) + stT211 71 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 70
    simpa using h
  have hprev := st211_p70
  have hstep := st211_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p72 : ((13643158563/6250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT211 (i+1))
      = (∑ i ∈ Finset.range 71, stT211 (i+1)) + stT211 72 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 71
    simpa using h
  have hprev := st211_p71
  have hstep := st211_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p73 : ((22886170086411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT211 (i+1))
      = (∑ i ∈ Finset.range 72, stT211 (i+1)) + stT211 73 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 72
    simpa using h
  have hprev := st211_p72
  have hstep := st211_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p74 : ((4401563282987/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT211 (i+1))
      = (∑ i ∈ Finset.range 73, stT211 (i+1)) + stT211 74 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 73
    simpa using h
  have hprev := st211_p73
  have hstep := st211_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p75 : ((4521700811327/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT211 (i+1))
      = (∑ i ∈ Finset.range 74, stT211 (i+1)) + stT211 75 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 74
    simpa using h
  have hprev := st211_p74
  have hstep := st211_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p76 : ((22380219276529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT211 (i+1))
      = (∑ i ∈ Finset.range 75, stT211 (i+1)) + stT211 76 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 75
    simpa using h
  have hprev := st211_p75
  have hstep := st211_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p77 : ((22172689046687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT211 (i+1))
      = (∑ i ∈ Finset.range 76, stT211 (i+1)) + stT211 77 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 76
    simpa using h
  have hprev := st211_p76
  have hstep := st211_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p78 : ((22813881659909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT211 (i+1))
      = (∑ i ∈ Finset.range 77, stT211 (i+1)) + stT211 78 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 77
    simpa using h
  have hprev := st211_p77
  have hstep := st211_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p79 : ((21834713073157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT211 (i+1))
      = (∑ i ∈ Finset.range 78, stT211 (i+1)) + stT211 79 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 78
    simpa using h
  have hprev := st211_p78
  have hstep := st211_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p80 : ((11476132100467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT211 (i+1))
      = (∑ i ∈ Finset.range 79, stT211 (i+1)) + stT211 80 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 79
    simpa using h
  have hprev := st211_p79
  have hstep := st211_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p81 : ((10986661708891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT211 (i+1))
      = (∑ i ∈ Finset.range 80, stT211 (i+1)) + stT211 81 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 80
    simpa using h
  have hprev := st211_p80
  have hstep := st211_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p82 : ((22527111991037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT211 (i+1))
      = (∑ i ∈ Finset.range 81, stT211 (i+1)) + stT211 82 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 81
    simpa using h
  have hprev := st211_p81
  have hstep := st211_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p83 : ((22591358074939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT211 (i+1))
      = (∑ i ∈ Finset.range 82, stT211 (i+1)) + stT211 83 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 82
    simpa using h
  have hprev := st211_p82
  have hstep := st211_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p84 : ((21910984901459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT211 (i+1))
      = (∑ i ∈ Finset.range 83, stT211 (i+1)) + stT211 84 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 83
    simpa using h
  have hprev := st211_p83
  have hstep := st211_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p85 : ((183688361439/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT211 (i+1))
      = (∑ i ∈ Finset.range 84, stT211 (i+1)) + stT211 85 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 84
    simpa using h
  have hprev := st211_p84
  have hstep := st211_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p86 : ((21976691308419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT211 (i+1))
      = (∑ i ∈ Finset.range 85, stT211 (i+1)) + stT211 86 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 85
    simpa using h
  have hprev := st211_p85
  have hstep := st211_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p87 : ((22440893290067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT211 (i+1))
      = (∑ i ∈ Finset.range 86, stT211 (i+1)) + stT211 87 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 86
    simpa using h
  have hprev := st211_p86
  have hstep := st211_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p88 : ((2842222290447/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT211 (i+1))
      = (∑ i ∈ Finset.range 87, stT211 (i+1)) + stT211 88 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 87
    simpa using h
  have hprev := st211_p87
  have hstep := st211_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p89 : ((10911873674083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT211 (i+1))
      = (∑ i ∈ Finset.range 88, stT211 (i+1)) + stT211 89 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 88
    simpa using h
  have hprev := st211_p88
  have hstep := st211_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p90 : ((2284425281477/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT211 (i+1))
      = (∑ i ∈ Finset.range 89, stT211 (i+1)) + stT211 90 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 89
    simpa using h
  have hprev := st211_p89
  have hstep := st211_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p91 : ((446689184797/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT211 (i+1))
      = (∑ i ∈ Finset.range 90, stT211 (i+1)) + stT211 91 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 90
    simpa using h
  have hprev := st211_p90
  have hstep := st211_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p92 : ((137492387569/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT211 (i+1))
      = (∑ i ∈ Finset.range 91, stT211 (i+1)) + stT211 92 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 91
    simpa using h
  have hprev := st211_p91
  have hstep := st211_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p93 : ((22960727234357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT211 (i+1))
      = (∑ i ∈ Finset.range 92, stT211 (i+1)) + stT211 93 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 92
    simpa using h
  have hprev := st211_p92
  have hstep := st211_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p94 : ((22056675537137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT211 (i+1))
      = (∑ i ∈ Finset.range 93, stT211 (i+1)) + stT211 94 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 93
    simpa using h
  have hprev := st211_p93
  have hstep := st211_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p95 : ((22219767051973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT211 (i+1))
      = (∑ i ∈ Finset.range 94, stT211 (i+1)) + stT211 95 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 94
    simpa using h
  have hprev := st211_p94
  have hstep := st211_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p96 : ((22932004677733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT211 (i+1))
      = (∑ i ∈ Finset.range 95, stT211 (i+1)) + stT211 96 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 95
    simpa using h
  have hprev := st211_p95
  have hstep := st211_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p97 : ((10964523978587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT211 (i+1))
      = (∑ i ∈ Finset.range 96, stT211 (i+1)) + stT211 97 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 96
    simpa using h
  have hprev := st211_p96
  have hstep := st211_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p98 : ((11178085263667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT211 (i+1))
      = (∑ i ∈ Finset.range 97, stT211 (i+1)) + stT211 98 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 97
    simpa using h
  have hprev := st211_p97
  have hstep := st211_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p99 : ((22892376862537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT211 (i+1))
      = (∑ i ∈ Finset.range 98, stT211 (i+1)) + stT211 99 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 98
    simpa using h
  have hprev := st211_p98
  have hstep := st211_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p100 : ((21892410862537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT211 (i+1))
      = (∑ i ∈ Finset.range 99, stT211 (i+1)) + stT211 100 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 99
    simpa using h
  have hprev := st211_p99
  have hstep := st211_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p101 : ((2238309246331/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT211 (i+1))
      = (∑ i ∈ Finset.range 100, stT211 (i+1)) + stT211 101 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 100
    simpa using h
  have hprev := st211_p100
  have hstep := st211_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p102 : ((11449029998417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT211 (i+1))
      = (∑ i ∈ Finset.range 101, stT211 (i+1)) + stT211 102 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 101
    simpa using h
  have hprev := st211_p101
  have hstep := st211_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p103 : ((10957205484907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT211 (i+1))
      = (∑ i ∈ Finset.range 102, stT211 (i+1)) + stT211 103 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 102
    simpa using h
  have hprev := st211_p102
  have hstep := st211_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p104 : ((11151980051467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT211 (i+1))
      = (∑ i ∈ Finset.range 103, stT211 (i+1)) + stT211 104 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 103
    simpa using h
  have hprev := st211_p103
  have hstep := st211_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p105 : ((11471436524917/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT211 (i+1))
      = (∑ i ∈ Finset.range 104, stT211 (i+1)) + stT211 105 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 104
    simpa using h
  have hprev := st211_p104
  have hstep := st211_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p106 : ((1375663636109/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT211 (i+1))
      = (∑ i ∈ Finset.range 105, stT211 (i+1)) + stT211 106 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 105
    simpa using h
  have hprev := st211_p105
  have hstep := st211_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p107 : ((172905348241/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT211 (i+1))
      = (∑ i ∈ Finset.range 106, stT211 (i+1)) + stT211 107 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 106
    simpa using h
  have hprev := st211_p106
  have hstep := st211_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p108 : ((11483965338049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT211 (i+1))
      = (∑ i ∈ Finset.range 107, stT211 (i+1)) + stT211 108 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 107
    simpa using h
  have hprev := st211_p107
  have hstep := st211_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p109 : ((277781703689/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT211 (i+1))
      = (∑ i ∈ Finset.range 108, stT211 (i+1)) + stT211 109 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 108
    simpa using h
  have hprev := st211_p108
  have hstep := st211_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p110 : ((21919938603199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT211 (i+1))
      = (∑ i ∈ Finset.range 109, stT211 (i+1)) + stT211 110 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 109
    simpa using h
  have hprev := st211_p109
  have hstep := st211_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p111 : ((5717232375181/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT211 (i+1))
      = (∑ i ∈ Finset.range 110, stT211 (i+1)) + stT211 111 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 110
    simpa using h
  have hprev := st211_p110
  have hstep := st211_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p112 : ((1127803598613/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT211 (i+1))
      = (∑ i ∈ Finset.range 111, stT211 (i+1)) + stT211 112 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 111
    simpa using h
  have hprev := st211_p111
  have hstep := st211_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p113 : ((21802711551667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT211 (i+1))
      = (∑ i ∈ Finset.range 112, stT211 (i+1)) + stT211 113 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 112
    simpa using h
  have hprev := st211_p112
  have hstep := st211_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p114 : ((22553693502217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT211 (i+1))
      = (∑ i ∈ Finset.range 113, stT211 (i+1)) + stT211 114 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 113
    simpa using h
  have hprev := st211_p113
  have hstep := st211_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p115 : ((22889416389809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT211 (i+1))
      = (∑ i ∈ Finset.range 114, stT211 (i+1)) + stT211 115 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 114
    simpa using h
  have hprev := st211_p114
  have hstep := st211_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p116 : ((21966742371059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT211 (i+1))
      = (∑ i ∈ Finset.range 115, stT211 (i+1)) + stT211 116 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 115
    simpa using h
  have hprev := st211_p115
  have hstep := st211_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p117 : ((22084783455559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT211 (i+1))
      = (∑ i ∈ Finset.range 116, stT211 (i+1)) + stT211 117 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 116
    simpa using h
  have hprev := st211_p116
  have hstep := st211_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p118 : ((22948535025409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT211 (i+1))
      = (∑ i ∈ Finset.range 117, stT211 (i+1)) + stT211 118 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 117
    simpa using h
  have hprev := st211_p117
  have hstep := st211_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p119 : ((22459353271243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT211 (i+1))
      = (∑ i ∈ Finset.range 118, stT211 (i+1)) + stT211 119 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 118
    simpa using h
  have hprev := st211_p118
  have hstep := st211_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p120 : ((21796210913487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT211 (i+1))
      = (∑ i ∈ Finset.range 119, stT211 (i+1)) + stT211 120 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 119
    simpa using h
  have hprev := st211_p119
  have hstep := st211_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p121 : ((22529233816827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT211 (i+1))
      = (∑ i ∈ Finset.range 120, stT211 (i+1)) + stT211 121 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 120
    simpa using h
  have hprev := st211_p120
  have hstep := st211_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p122 : ((11468377912869/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT211 (i+1))
      = (∑ i ∈ Finset.range 121, stT211 (i+1)) + stT211 122 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 121
    simpa using h
  have hprev := st211_p121
  have hstep := st211_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p123 : ((11039744733279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT211 (i+1))
      = (∑ i ∈ Finset.range 122, stT211 (i+1)) + stT211 123 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 122
    simpa using h
  have hprev := st211_p122
  have hstep := st211_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p124 : ((21920803605523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT211 (i+1))
      = (∑ i ∈ Finset.range 123, stT211 (i+1)) + stT211 124 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 123
    simpa using h
  have hprev := st211_p123
  have hstep := st211_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p125 : ((22813901487001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT211 (i+1))
      = (∑ i ∈ Finset.range 124, stT211 (i+1)) + stT211 125 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 124
    simpa using h
  have hprev := st211_p124
  have hstep := st211_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p126 : ((11381594327663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT211 (i+1))
      = (∑ i ∈ Finset.range 125, stT211 (i+1)) + stT211 126 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 125
    simpa using h
  have hprev := st211_p125
  have hstep := st211_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p127 : ((5471575173303/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT211 (i+1))
      = (∑ i ∈ Finset.range 126, stT211 (i+1)) + stT211 127 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 126
    simpa using h
  have hprev := st211_p126
  have hstep := st211_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p128 : ((2761851970497/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT211 (i+1))
      = (∑ i ∈ Finset.range 127, stT211 (i+1)) + stT211 128 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 127
    simpa using h
  have hprev := st211_p127
  have hstep := st211_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p129 : ((11466700623463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT211 (i+1))
      = (∑ i ∈ Finset.range 128, stT211 (i+1)) + stT211 129 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 128
    simpa using h
  have hprev := st211_p128
  have hstep := st211_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p130 : ((5654459293211/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT211 (i+1))
      = (∑ i ∈ Finset.range 129, stT211 (i+1)) + stT211 130 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 129
    simpa using h
  have hprev := st211_p129
  have hstep := st211_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p131 : ((2727240662143/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT211 (i+1))
      = (∑ i ∈ Finset.range 130, stT211 (i+1)) + stT211 131 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 130
    simpa using h
  have hprev := st211_p130
  have hstep := st211_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p132 : ((2774347801479/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT211 (i+1))
      = (∑ i ∈ Finset.range 131, stT211 (i+1)) + stT211 132 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 131
    simpa using h
  have hprev := st211_p131
  have hstep := st211_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p133 : ((5742004547873/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT211 (i+1))
      = (∑ i ∈ Finset.range 132, stT211 (i+1)) + stT211 133 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 132
    simpa using h
  have hprev := st211_p132
  have hstep := st211_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p134 : ((1410602488683/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT211 (i+1))
      = (∑ i ∈ Finset.range 133, stT211 (i+1)) + stT211 134 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 133
    simpa using h
  have hprev := st211_p133
  have hstep := st211_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p135 : ((2180509049879/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT211 (i+1))
      = (∑ i ∈ Finset.range 134, stT211 (i+1)) + stT211 135 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 134
    simpa using h
  have hprev := st211_p134
  have hstep := st211_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p136 : ((11094255593327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT211 (i+1))
      = (∑ i ∈ Finset.range 135, stT211 (i+1)) + stT211 136 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 135
    simpa using h
  have hprev := st211_p135
  have hstep := st211_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p137 : ((2870243150041/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT211 (i+1))
      = (∑ i ∈ Finset.range 136, stT211 (i+1)) + stT211 137 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 136
    simpa using h
  have hprev := st211_p136
  have hstep := st211_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p138 : ((11314271793111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT211 (i+1))
      = (∑ i ∈ Finset.range 137, stT211 (i+1)) + stT211 138 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 137
    simpa using h
  have hprev := st211_p137
  have hstep := st211_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p139 : ((5458304703459/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT211 (i+1))
      = (∑ i ∈ Finset.range 138, stT211 (i+1)) + stT211 139 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 138
    simpa using h
  have hprev := st211_p138
  have hstep := st211_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p140 : ((11040184866759/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT211 (i+1))
      = (∑ i ∈ Finset.range 139, stT211 (i+1)) + stT211 140 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 139
    simpa using h
  have hprev := st211_p139
  have hstep := st211_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p141 : ((11450361248517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT211 (i+1))
      = (∑ i ∈ Finset.range 140, stT211 (i+1)) + stT211 141 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 140
    simpa using h
  have hprev := st211_p140
  have hstep := st211_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p142 : ((11388392692909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT211 (i+1))
      = (∑ i ∈ Finset.range 141, stT211 (i+1)) + stT211 142 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 141
    simpa using h
  have hprev := st211_p141
  have hstep := st211_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p143 : ((21941911315609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT211 (i+1))
      = (∑ i ∈ Finset.range 142, stT211 (i+1)) + stT211 143 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 142
    simpa using h
  have hprev := st211_p142
  have hstep := st211_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p144 : ((4381322090807/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT211 (i+1))
      = (∑ i ∈ Finset.range 143, stT211 (i+1)) + stT211 144 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 143
    simpa using h
  have hprev := st211_p143
  have hstep := st211_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p145 : ((22727334854971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT211 (i+1))
      = (∑ i ∈ Finset.range 144, stT211 (i+1)) + stT211 145 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 144
    simpa using h
  have hprev := st211_p144
  have hstep := st211_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p146 : ((22950839516481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT211 (i+1))
      = (∑ i ∈ Finset.range 145, stT211 (i+1)) + stT211 146 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 145
    simpa using h
  have hprev := st211_p145
  have hstep := st211_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p147 : ((22192423126371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT211 (i+1))
      = (∑ i ∈ Finset.range 146, stT211 (i+1)) + stT211 147 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 146
    simpa using h
  have hprev := st211_p146
  have hstep := st211_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p148 : ((10883361300903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT211 (i+1))
      = (∑ i ∈ Finset.range 147, stT211 (i+1)) + stT211 148 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 147
    simpa using h
  have hprev := st211_p147
  have hstep := st211_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p149 : ((2799537907971/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT211 (i+1))
      = (∑ i ∈ Finset.range 148, stT211 (i+1)) + stT211 149 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 148
    simpa using h
  have hprev := st211_p148
  have hstep := st211_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p150 : ((2876456015713/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT211 (i+1))
      = (∑ i ∈ Finset.range 149, stT211 (i+1)) + stT211 150 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 149
    simpa using h
  have hprev := st211_p149
  have hstep := st211_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p151 : ((11293697753167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT211 (i+1))
      = (∑ i ∈ Finset.range 150, stT211 (i+1)) + stT211 151 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 150
    simpa using h
  have hprev := st211_p150
  have hstep := st211_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p152 : ((2183122547339/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT211 (i+1))
      = (∑ i ∈ Finset.range 151, stT211 (i+1)) + stT211 152 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 151
    simpa using h
  have hprev := st211_p151
  have hstep := st211_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p153 : ((2197840011773/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT211 (i+1))
      = (∑ i ∈ Finset.range 152, stT211 (i+1)) + stT211 153 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 152
    simpa using h
  have hprev := st211_p152
  have hstep := st211_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p154 : ((11392056262969/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT211 (i+1))
      = (∑ i ∈ Finset.range 153, stT211 (i+1)) + stT211 154 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 153
    simpa using h
  have hprev := st211_p153
  have hstep := st211_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p155 : ((11478964558769/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT211 (i+1))
      = (∑ i ∈ Finset.range 154, stT211 (i+1)) + stT211 155 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 154
    simpa using h
  have hprev := st211_p154
  have hstep := st211_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p156 : ((1111541029413/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT211 (i+1))
      = (∑ i ∈ Finset.range 155, stT211 (i+1)) + stT211 156 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 155
    simpa using h
  have hprev := st211_p155
  have hstep := st211_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p157 : ((21744871000569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT211 (i+1))
      = (∑ i ∈ Finset.range 156, stT211 (i+1)) + stT211 157 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 156
    simpa using h
  have hprev := st211_p156
  have hstep := st211_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p158 : ((11124103990557/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT211 (i+1))
      = (∑ i ∈ Finset.range 157, stT211 (i+1)) + stT211 158 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 157
    simpa using h
  have hprev := st211_p157
  have hstep := st211_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p159 : ((22963805655199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT211 (i+1))
      = (∑ i ∈ Finset.range 158, stT211 (i+1)) + stT211 159 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 158
    simpa using h
  have hprev := st211_p158
  have hstep := st211_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p160 : ((22808553518599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT211 (i+1))
      = (∑ i ∈ Finset.range 159, stT211 (i+1)) + stT211 160 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 159
    simpa using h
  have hprev := st211_p159
  have hstep := st211_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p161 : ((2752719143399/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT211 (i+1))
      = (∑ i ∈ Finset.range 160, stT211 (i+1)) + stT211 161 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 160
    simpa using h
  have hprev := st211_p160
  have hstep := st211_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p162 : ((21772456112667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT211 (i+1))
      = (∑ i ∈ Finset.range 161, stT211 (i+1)) + stT211 162 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 161
    simpa using h
  have hprev := st211_p161
  have hstep := st211_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p163 : ((22421004791787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT211 (i+1))
      = (∑ i ∈ Finset.range 162, stT211 (i+1)) + stT211 163 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 162
    simpa using h
  have hprev := st211_p162
  have hstep := st211_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p164 : ((4604106519403/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT211 (i+1))
      = (∑ i ∈ Finset.range 163, stT211 (i+1)) + stT211 164 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 163
    simpa using h
  have hprev := st211_p163
  have hstep := st211_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p165 : ((11356075618819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT211 (i+1))
      = (∑ i ∈ Finset.range 164, stT211 (i+1)) + stT211 165 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 164
    simpa using h
  have hprev := st211_p164
  have hstep := st211_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p166 : ((21940769685533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT211 (i+1))
      = (∑ i ∈ Finset.range 165, stT211 (i+1)) + stT211 166 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 165
    simpa using h
  have hprev := st211_p165
  have hstep := st211_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p167 : ((21792958467997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT211 (i+1))
      = (∑ i ∈ Finset.range 166, stT211 (i+1)) + stT211 167 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 166
    simpa using h
  have hprev := st211_p166
  have hstep := st211_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p168 : ((22468783338517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT211 (i+1))
      = (∑ i ∈ Finset.range 167, stT211 (i+1)) + stT211 168 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 167
    simpa using h
  have hprev := st211_p167
  have hstep := st211_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p169 : ((23032108929037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT211 (i+1))
      = (∑ i ∈ Finset.range 168, stT211 (i+1)) + stT211 169 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 168
    simpa using h
  have hprev := st211_p168
  have hstep := st211_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p170 : ((11358604603151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT211 (i+1))
      = (∑ i ∈ Finset.range 169, stT211 (i+1)) + stT211 170 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 169
    simpa using h
  have hprev := st211_p169
  have hstep := st211_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p171 : ((10977765248871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT211 (i+1))
      = (∑ i ∈ Finset.range 170, stT211 (i+1)) + stT211 171 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 170
    simpa using h
  have hprev := st211_p170
  have hstep := st211_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p172 : ((21766329297187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT211 (i+1))
      = (∑ i ∈ Finset.range 171, stT211 (i+1)) + stT211 172 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 171
    simpa using h
  have hprev := st211_p171
  have hstep := st211_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p173 : ((22394505655017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT211 (i+1))
      = (∑ i ∈ Finset.range 172, stT211 (i+1)) + stT211 173 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 172
    simpa using h
  have hprev := st211_p172
  have hstep := st211_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p174 : ((23012422237641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT211 (i+1))
      = (∑ i ∈ Finset.range 173, stT211 (i+1)) + stT211 174 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 173
    simpa using h
  have hprev := st211_p173
  have hstep := st211_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p175 : ((11410409590899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT211 (i+1))
      = (∑ i ∈ Finset.range 174, stT211 (i+1)) + stT211 175 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 174
    simpa using h
  have hprev := st211_p174
  have hstep := st211_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p176 : ((5517937825137/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT211 (i+1))
      = (∑ i ∈ Finset.range 175, stT211 (i+1)) + stT211 176 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 175
    simpa using h
  have hprev := st211_p175
  have hstep := st211_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p177 : ((2171954905917/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT211 (i+1))
      = (∑ i ∈ Finset.range 176, stT211 (i+1)) + stT211 177 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 176
    simpa using h
  have hprev := st211_p176
  have hstep := st211_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p178 : ((693844063929/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT211 (i+1))
      = (∑ i ∈ Finset.range 177, stT211 (i+1)) + stT211 178 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 177
    simpa using h
  have hprev := st211_p177
  have hstep := st211_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p179 : ((5728557581277/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT211 (i+1))
      = (∑ i ∈ Finset.range 178, stT211 (i+1)) + stT211 179 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 178
    simpa using h
  have hprev := st211_p178
  have hstep := st211_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p180 : ((22975922613103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT211 (i+1))
      = (∑ i ∈ Finset.range 179, stT211 (i+1)) + stT211 180 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 179
    simpa using h
  have hprev := st211_p179
  have hstep := st211_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p181 : ((11159108644529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT211 (i+1))
      = (∑ i ∈ Finset.range 180, stT211 (i+1)) + stT211 181 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 180
    simpa using h
  have hprev := st211_p180
  have hstep := st211_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p182 : ((10870389545779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT211 (i+1))
      = (∑ i ∈ Finset.range 181, stT211 (i+1)) + stT211 182 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 181
    simpa using h
  have hprev := st211_p181
  have hstep := st211_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p183 : ((1370815562201/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT211 (i+1))
      = (∑ i ∈ Finset.range 182, stT211 (i+1)) + stT211 183 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 182
    simpa using h
  have hprev := st211_p182
  have hstep := st211_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p184 : ((5665266618351/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT211 (i+1))
      = (∑ i ∈ Finset.range 183, stT211 (i+1)) + stT211 184 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 183
    simpa using h
  have hprev := st211_p183
  have hstep := st211_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p185 : ((11533479871227/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT211 (i+1))
      = (∑ i ∈ Finset.range 184, stT211 (i+1)) + stT211 185 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 184
    simpa using h
  have hprev := st211_p184
  have hstep := st211_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p186 : ((11341039150083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT211 (i+1))
      = (∑ i ∈ Finset.range 185, stT211 (i+1)) + stT211 186 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 185
    simpa using h
  have hprev := st211_p185
  have hstep := st211_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p187 : ((4391088752961/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT211 (i+1))
      = (∑ i ∈ Finset.range 186, stT211 (i+1)) + stT211 187 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 186
    simpa using h
  have hprev := st211_p186
  have hstep := st211_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p188 : ((2171746282933/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT211 (i+1))
      = (∑ i ∈ Finset.range 187, stT211 (i+1)) + stT211 188 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 187
    simpa using h
  have hprev := st211_p187
  have hstep := st211_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p189 : ((11116307104697/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT211 (i+1))
      = (∑ i ∈ Finset.range 188, stT211 (i+1)) + stT211 189 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 188
    simpa using h
  have hprev := st211_p188
  have hstep := st211_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p190 : ((11459490987331/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT211 (i+1))
      = (∑ i ∈ Finset.range 189, stT211 (i+1)) + stT211 190 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 189
    simpa using h
  have hprev := st211_p189
  have hstep := st211_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p191 : ((11507621682663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT211 (i+1))
      = (∑ i ∈ Finset.range 190, stT211 (i+1)) + stT211 191 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 190
    simpa using h
  have hprev := st211_p190
  have hstep := st211_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p192 : ((11210288030883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT211 (i+1))
      = (∑ i ∈ Finset.range 191, stT211 (i+1)) + stT211 192 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 191
    simpa using h
  have hprev := st211_p191
  have hstep := st211_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p193 : ((10893330731787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT211 (i+1))
      = (∑ i ∈ Finset.range 192, stT211 (i+1)) + stT211 193 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 192
    simpa using h
  have hprev := st211_p192
  have hstep := st211_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p194 : ((10898085767621/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT211 (i+1))
      = (∑ i ∈ Finset.range 193, stT211 (i+1)) + stT211 194 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 193
    simpa using h
  have hprev := st211_p193
  have hstep := st211_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p195 : ((11216866779177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT211 (i+1))
      = (∑ i ∈ Finset.range 194, stT211 (i+1)) + stT211 195 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 194
    simpa using h
  have hprev := st211_p194
  have hstep := st211_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p196 : ((23020539400119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT211 (i+1))
      = (∑ i ∈ Finset.range 195, stT211 (i+1)) + stT211 196 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 195
    simpa using h
  have hprev := st211_p195
  have hstep := st211_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p197 : ((22942555174343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT211 (i+1))
      = (∑ i ∈ Finset.range 196, stT211 (i+1)) + stT211 197 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 196
    simpa using h
  have hprev := st211_p196
  have hstep := st211_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p198 : ((22285977821393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT211 (i+1))
      = (∑ i ∈ Finset.range 197, stT211 (i+1)) + stT211 198 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 197
    simpa using h
  have hprev := st211_p197
  have hstep := st211_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p199 : ((21730376667371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT211 (i+1))
      = (∑ i ∈ Finset.range 198, stT211 (i+1)) + stT211 199 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 198
    simpa using h
  have hprev := st211_p198
  have hstep := st211_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p200 : ((21840902992019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT211 (i+1))
      = (∑ i ∈ Finset.range 199, stT211 (i+1)) + stT211 200 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 199
    simpa using h
  have hprev := st211_p199
  have hstep := st211_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p201 : ((2812580841553/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT211 (i+1))
      = (∑ i ∈ Finset.range 200, stT211 (i+1)) + stT211 201 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 200
    simpa using h
  have hprev := st211_p200
  have hstep := st211_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p202 : ((11522585150541/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT211 (i+1))
      = (∑ i ∈ Finset.range 201, stT211 (i+1)) + stT211 202 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 201
    simpa using h
  have hprev := st211_p201
  have hstep := st211_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p203 : ((22935461393689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT211 (i+1))
      = (∑ i ∈ Finset.range 202, stT211 (i+1)) + stT211 203 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 202
    simpa using h
  have hprev := st211_p202
  have hstep := st211_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p204 : ((1114223199531/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT211 (i+1))
      = (∑ i ∈ Finset.range 203, stT211 (i+1)) + stT211 204 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 203
    simpa using h
  have hprev := st211_p203
  have hstep := st211_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p205 : ((21730434298301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT211 (i+1))
      = (∑ i ∈ Finset.range 204, stT211 (i+1)) + stT211 205 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 204
    simpa using h
  have hprev := st211_p204
  have hstep := st211_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p206 : ((4361477412937/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT211 (i+1))
      = (∑ i ∈ Finset.range 205, stT211 (i+1)) + stT211 206 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 205
    simpa using h
  have hprev := st211_p205
  have hstep := st211_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p207 : ((22436705070373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT211 (i+1))
      = (∑ i ∈ Finset.range 206, stT211 (i+1)) + stT211 207 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 206
    simpa using h
  have hprev := st211_p206
  have hstep := st211_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p208 : ((5754297054937/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT211 (i+1))
      = (∑ i ∈ Finset.range 207, stT211 (i+1)) + stT211 208 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 207
    simpa using h
  have hprev := st211_p207
  have hstep := st211_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p209 : ((23003465285863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT211 (i+1))
      = (∑ i ∈ Finset.range 208, stT211 (i+1)) + stT211 209 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 208
    simpa using h
  have hprev := st211_p208
  have hstep := st211_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p210 : ((4482584396903/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT211 (i+1))
      = (∑ i ∈ Finset.range 209, stT211 (i+1)) + stT211 210 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 209
    simpa using h
  have hprev := st211_p209
  have hstep := st211_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p211 : ((85138955431/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT211 (i+1))
      = (∑ i ∈ Finset.range 210, stT211 (i+1)) + stT211 211 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 210
    simpa using h
  have hprev := st211_p210
  have hstep := st211_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p212 : ((21716982409849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT211 (i+1))
      = (∑ i ∈ Finset.range 211, stT211 (i+1)) + stT211 212 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 211
    simpa using h
  have hprev := st211_p211
  have hstep := st211_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p213 : ((22244312687281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT211 (i+1))
      = (∑ i ∈ Finset.range 212, stT211 (i+1)) + stT211 213 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 212
    simpa using h
  have hprev := st211_p212
  have hstep := st211_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p214 : ((11449085313193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT211 (i+1))
      = (∑ i ∈ Finset.range 213, stT211 (i+1)) + stT211 214 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 213
    simpa using h
  have hprev := st211_p213
  have hstep := st211_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p215 : ((1154699953277/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT211 (i+1))
      = (∑ i ∈ Finset.range 214, stT211 (i+1)) + stT211 215 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 214
    simpa using h
  have hprev := st211_p214
  have hstep := st211_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p216 : ((11330997685779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT211 (i+1))
      = (∑ i ∈ Finset.range 215, stT211 (i+1)) + stT211 216 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 215
    simpa using h
  have hprev := st211_p215
  have hstep := st211_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p217 : ((10992981752619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT211 (i+1))
      = (∑ i ∈ Finset.range 216, stT211 (i+1)) + stT211 217 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 216
    simpa using h
  have hprev := st211_p216
  have hstep := st211_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p218 : ((10827925122561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT211 (i+1))
      = (∑ i ∈ Finset.range 217, stT211 (i+1)) + stT211 218 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 217
    simpa using h
  have hprev := st211_p217
  have hstep := st211_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p219 : ((10976881883893/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT211 (i+1))
      = (∑ i ∈ Finset.range 218, stT211 (i+1)) + stT211 219 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 218
    simpa using h
  have hprev := st211_p218
  have hstep := st211_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p220 : ((11310031926151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT211 (i+1))
      = (∑ i ∈ Finset.range 219, stT211 (i+1)) + stT211 220 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 219
    simpa using h
  have hprev := st211_p219
  have hstep := st211_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p221 : ((11543368389511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT211 (i+1))
      = (∑ i ∈ Finset.range 220, stT211 (i+1)) + stT211 221 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 220
    simpa using h
  have hprev := st211_p220
  have hstep := st211_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p222 : ((22962708978893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT211 (i+1))
      = (∑ i ∈ Finset.range 221, stT211 (i+1)) + stT211 222 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 221
    simpa using h
  have hprev := st211_p221
  have hstep := st211_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p223 : ((22355860095193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT211 (i+1))
      = (∑ i ∈ Finset.range 222, stT211 (i+1)) + stT211 223 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 222
    simpa using h
  have hprev := st211_p222
  have hstep := st211_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p224 : ((21771857418877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT211 (i+1))
      = (∑ i ∈ Finset.range 223, stT211 (i+1)) + stT211 224 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 223
    simpa using h
  have hprev := st211_p223
  have hstep := st211_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p225 : ((2168969671113/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT211 (i+1))
      = (∑ i ∈ Finset.range 224, stT211 (i+1)) + stT211 225 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 224
    simpa using h
  have hprev := st211_p224
  have hstep := st211_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p226 : ((2217245303211/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT211 (i+1))
      = (∑ i ∈ Finset.range 225, stT211 (i+1)) + stT211 226 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 225
    simpa using h
  have hprev := st211_p225
  have hstep := st211_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p227 : ((22826239435077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT211 (i+1))
      = (∑ i ∈ Finset.range 226, stT211 (i+1)) + stT211 227 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 226
    simpa using h
  have hprev := st211_p226
  have hstep := st211_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p228 : ((23126349908839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT211 (i+1))
      = (∑ i ∈ Finset.range 227, stT211 (i+1)) + stT211 228 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 227
    simpa using h
  have hprev := st211_p227
  have hstep := st211_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p229 : ((5709265959007/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT211 (i+1))
      = (∑ i ∈ Finset.range 228, stT211 (i+1)) + stT211 229 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 228
    simpa using h
  have hprev := st211_p228
  have hstep := st211_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p230 : ((1386911105679/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT211 (i+1))
      = (∑ i ∈ Finset.range 229, stT211 (i+1)) + stT211 230 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 229
    simpa using h
  have hprev := st211_p229
  have hstep := st211_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p231 : ((1355913629933/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT211 (i+1))
      = (∑ i ∈ Finset.range 230, stT211 (i+1)) + stT211 231 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 230
    simpa using h
  have hprev := st211_p230
  have hstep := st211_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p232 : ((2716555439197/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT211 (i+1))
      = (∑ i ∈ Finset.range 231, stT211 (i+1)) + stT211 232 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 231
    simpa using h
  have hprev := st211_p231
  have hstep := st211_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p233 : ((4454207497237/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT211 (i+1))
      = (∑ i ∈ Finset.range 232, stT211 (i+1)) + stT211 233 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 232
    simpa using h
  have hprev := st211_p232
  have hstep := st211_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p234 : ((36633435289/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT211 (i+1))
      = (∑ i ∈ Finset.range 233, stT211 (i+1)) + stT211 234 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 233
    simpa using h
  have hprev := st211_p233
  have hstep := st211_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p235 : ((23133534927401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT211 (i+1))
      = (∑ i ∈ Finset.range 234, stT211 (i+1)) + stT211 235 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 234
    simpa using h
  have hprev := st211_p234
  have hstep := st211_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p236 : ((22808343635641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT211 (i+1))
      = (∑ i ∈ Finset.range 235, stT211 (i+1)) + stT211 236 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 235
    simpa using h
  have hprev := st211_p235
  have hstep := st211_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p237 : ((22166587313171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT211 (i+1))
      = (∑ i ∈ Finset.range 236, stT211 (i+1)) + stT211 237 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 236
    simpa using h
  have hprev := st211_p236
  have hstep := st211_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p238 : ((21684756537443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT211 (i+1))
      = (∑ i ∈ Finset.range 237, stT211 (i+1)) + stT211 238 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 237
    simpa using h
  have hprev := st211_p237
  have hstep := st211_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p239 : ((4342989226791/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT211 (i+1))
      = (∑ i ∈ Finset.range 238, stT211 (i+1)) + stT211 239 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 238
    simpa using h
  have hprev := st211_p238
  have hstep := st211_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p240 : ((22231487034289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT211 (i+1))
      = (∑ i ∈ Finset.range 239, stT211 (i+1)) + stT211 240 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 239
    simpa using h
  have hprev := st211_p239
  have hstep := st211_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p241 : ((22858011840413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT211 (i+1))
      = (∑ i ∈ Finset.range 240, stT211 (i+1)) + stT211 241 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 240
    simpa using h
  have hprev := st211_p240
  have hstep := st211_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p242 : ((4628994080497/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT211 (i+1))
      = (∑ i ∈ Finset.range 241, stT211 (i+1)) + stT211 242 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 241
    simpa using h
  have hprev := st211_p241
  have hstep := st211_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p243 : ((28613521661/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT211 (i+1))
      = (∑ i ∈ Finset.range 242, stT211 (i+1)) + stT211 243 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 242
    simpa using h
  have hprev := st211_p242
  have hstep := st211_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p244 : ((4455724115363/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT211 (i+1))
      = (∑ i ∈ Finset.range 243, stT211 (i+1)) + stT211 244 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 243
    simpa using h
  have hprev := st211_p243
  have hstep := st211_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p245 : ((42459668459/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT211 (i+1))
      = (∑ i ∈ Finset.range 244, stT211 (i+1)) + stT211 245 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 244
    simpa using h
  have hprev := st211_p244
  have hstep := st211_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p246 : ((10823502436741/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT211 (i+1))
      = (∑ i ∈ Finset.range 245, stT211 (i+1)) + stT211 246 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 245
    simpa using h
  have hprev := st211_p245
  have hstep := st211_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p247 : ((11031027735909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT211 (i+1))
      = (∑ i ∈ Finset.range 246, stT211 (i+1)) + stT211 247 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 246
    simpa using h
  have hprev := st211_p246
  have hstep := st211_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p248 : ((11348502653409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT211 (i+1))
      = (∑ i ∈ Finset.range 247, stT211 (i+1)) + stT211 248 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 247
    simpa using h
  have hprev := st211_p247
  have hstep := st211_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p249 : ((11559626219699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT211 (i+1))
      = (∑ i ∈ Finset.range 248, stT211 (i+1)) + stT211 249 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 248
    simpa using h
  have hprev := st211_p248
  have hstep := st211_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_p250 : ((11522880526099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT211 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT211 (i+1))
      = (∑ i ∈ Finset.range 249, stT211 (i+1)) + stT211 250 := by
    have h := Finset.sum_range_succ (fun i => stT211 (i+1)) 249
    simpa using h
  have hprev := st211_p249
  have hstep := st211_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st211_s250 :
    |Real.sin (((211 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((95177/100000 : ℚ) : ℝ))
      - ((62077/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 2109011/5000000) (δ := 1073/100000000) (ψ := 95177/100000) 211 185
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 211`** (evaluated boundary). -/
theorem station_211_sign : 0 < hardyG ((((211:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 211 250 (by norm_num) (by norm_num)
    ((95177/100000 : ℚ) : ℝ)
  have hchain := st211_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT211 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((211 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((95177/100000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st211_c250
  have hsinb := abs_le.mp st211_s250
  have hbdy_lo : ((-4141093650441/55651562500000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((211 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((95177/100000 : ℚ) : ℝ))) / 2
          - ((((211:ℕ)):ℝ))
            * Real.sin (((211 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((95177/100000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((211:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((211:ℝ) * Real.log (250:ℝ) - ((95177/100000 : ℚ) : ℝ))) / 2
        - ((211:ℝ)) * Real.sin ((211:ℝ) * Real.log (250:ℝ) - ((95177/100000 : ℚ) : ℝ))
        ≥ ((-52381113/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((211:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-52381113/250000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-52381113/250000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-52381113/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((211:ℕ)):ℝ))+1) * (((((211:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((154579282473/156250000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((11522880526099/5000000000000 : ℚ) : ℝ) + ((-4141093650441/55651562500000 : ℚ) : ℝ)
      - ((154579282473/156250000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((95177/100000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((211:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((95177/100000 : ℚ) : ℝ)
        * (riemannZeta (line ((((211:ℕ)):ℝ)))).re
      - Real.sin ((95177/100000 : ℚ) : ℝ)
        * (riemannZeta (line ((((211:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((211:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((211:ℕ)):ℝ))
      = (((((211:ℕ)):ℝ)) * (Real.log ((((211:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((211:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_211
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
  have hθwin : |(((95177/100000 : ℚ) : ℝ) + ((42:ℤ)) * (2*Real.pi)) - theta ((((211:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((211:ℕ)):ℝ)))
    (φ := ((95177/100000 : ℚ) : ℝ) + ((42:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((95177/100000 : ℚ)) : ℝ) 42).1,
    (cos_sin_shift (((95177/100000 : ℚ)) : ℝ) 42).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_211_sign
end AxiomAudit
