import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 262` (rung-262.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT262 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((262 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-414889/500000 : ℚ) : ℝ))

theorem st262_c1 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((4219/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 414889/2000000) (δ := 1/1000000000) (ψ := -414889/500000) 262 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t1 : ((67499/100000 : ℚ) : ℝ) ≤ stT262 1 := by
  have hc : ((67499/100000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67499/100000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((67499/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c2 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((243867/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 554893/10000000) (δ := 13293/1000000000) (ψ := -414889/500000) 262 29
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t2 : ((3448623015503/5000000000000 : ℚ) : ℝ) ≤ stT262 2 := by
  have hc : ((487709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3448623015503/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((487709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c3 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((467889/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -450421/5000000) (δ := 13271/1000000000) (ψ := -414889/500000) 262 46
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t3 : ((168825858733/312500000000 : ℚ) : ℝ) ≤ stT262 3 := by
  have hc : ((58483/62500 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168825858733/312500000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((58483/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c4 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((926479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7717/80000) (δ := 6609/500000000) (ψ := -414889/500000) 262 58
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t4 : ((926429/2000000 : ℚ) : ℝ) ≤ stT262 4 := by
  have hc : ((926429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((926429/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((926429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c5 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((41679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3822763/10000000) (δ := 661/50000000) (ψ := -414889/500000) 262 67
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t5 : ((37234101583/2000000000000 : ℚ) : ℝ) ≤ stT262 5 := by
  have hc : ((41629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37234101583/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((41629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c6 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((56683/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -60509/250000) (δ := 331/25000000) (ψ := -414889/500000) 262 75
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t6 : ((57846728699/250000000000 : ℚ) : ℝ) ≤ stT262 6 := by
  have hc : ((28339/50000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57846728699/250000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((28339/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c7 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-37219/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4300569/10000000) (δ := 13283/1000000000) (ψ := -414889/500000) 262 81
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t7 : ((-56288741127/1000000000000 : ℚ) : ℝ) ≤ stT262 7 := by
  have hc : ((-74463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56288741127/1000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-74463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c8 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((136407/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -155259/625000) (δ := 6563/500000000) (ψ := -414889/500000) 262 87
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t8 : ((964454511537/5000000000000 : ℚ) : ℝ) ≤ stT262 8 := by
  have hc : ((272789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((964454511537/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((272789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c9 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((20357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -775219/2000000) (δ := 6631/500000000) (ψ := -414889/500000) 262 92
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t9 : ((67689993231/10000000000000 : ℚ) : ℝ) ≤ stT262 9 := by
  have hc : ((20307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67689993231/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((20307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c10 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((75601/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2303179/10000000) (δ := 1639/125000000) (ψ := -414889/500000) 262 96
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t10 : ((956206156983/5000000000000 : ℚ) : ℝ) ≤ stT262 10 := by
  have hc : ((302379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((956206156983/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((302379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c11 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((181243/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1899507/10000000) (δ := 13119/1000000000) (ψ := -414889/500000) 262 100
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t11 : ((1092860873093/5000000000000 : ℚ) : ℝ) ≤ stT262 11 := by
  have hc : ((362461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1092860873093/5000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((362461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c12 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-1031/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3939879/10000000) (δ := 3287/250000000) (ψ := -414889/500000) 262 104
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t12 : ((-93909651/62500000000 : ℚ) : ℝ) ≤ stT262 12 := by
  have hc : ((-1041/200000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93909651/62500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-1041/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c13 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((34191/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6821/50000) (δ := 1327/100000000) (ψ := -414889/500000) 262 107
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t13 : ((189646383/800000000 : ℚ) : ℝ) ≤ stT262 13 := by
  have hc : ((34189/40000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189646383/800000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((34189/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c14 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((442493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55621/200000) (δ := 13191/1000000000) (ψ := -414889/500000) 262 110
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t14 : ((295619617779/2500000000000 : ℚ) : ℝ) ≤ stT262 14 := by
  have hc : ((442443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((295619617779/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((442443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c15 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((471543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 847509/10000000) (δ := 1329/100000000) (ψ := -414889/500000) 262 113
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t15 : ((152181727223/625000000000 : ℚ) : ℝ) ≤ stT262 15 := by
  have hc : ((235759/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152181727223/625000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((235759/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c16 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-3833/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4003663/10000000) (δ := 13169/1000000000) (ψ := -414889/500000) 262 116
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t16 : ((-38392515357/5000000000000 : ℚ) : ℝ) ≤ stT262 16 := by
  have hc : ((-15357/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38392515357/5000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-15357/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c17 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-72253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1072381/2500000) (δ := 13249/1000000000) (ψ := -414889/500000) 262 118
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t17 : ((-87649976623/2500000000000 : ℚ) : ℝ) ≤ stT262 17 := by
  have hc : ((-36139/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87649976623/2500000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-36139/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c18 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-1732/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2697807/5000000) (δ := 1317/100000000) (ψ := -414889/500000) 262 121
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t18 : ((-130647427867/1000000000000 : ℚ) : ℝ) ≤ stT262 18 := by
  have hc : ((-55429/100000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130647427867/1000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-55429/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c19 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((847781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55901/400000) (δ := 6609/500000000) (ψ := -414889/500000) 262 123
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t19 : ((1944828007767/10000000000000 : ℚ) : ℝ) ≤ stT262 19 := by
  have hc : ((847731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1944828007767/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((847731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c20 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((951271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39183/500000) (δ := 3301/250000000) (ψ := -414889/500000) 262 125
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t20 : ((2126993887807/10000000000000 : ℚ) : ℝ) ≤ stT262 20 := by
  have hc : ((951221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2126993887807/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((951221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c21 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((862743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 265063/2000000) (δ := 13213/1000000000) (ψ := -414889/500000) 262 127
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t21 : ((941274842677/5000000000000 : ℚ) : ℝ) ≤ stT262 21 := by
  have hc : ((862693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((941274842677/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((862693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c22 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((988471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94997/2500000) (δ := 527/40000000) (ψ := -414889/500000) 262 129
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t22 : ((2107320490947/10000000000000 : ℚ) : ℝ) ≤ stT262 22 := by
  have hc : ((988421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2107320490947/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((988421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c23 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((719299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1920009/10000000) (δ := 6621/500000000) (ψ := -414889/500000) 262 131
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t23 : ((187467217107/1250000000000 : ℚ) : ℝ) ≤ stT262 23 := by
  have hc : ((719249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187467217107/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((719249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c24 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-575293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2729699/5000000) (δ := 13147/1000000000) (ψ := -414889/500000) 262 133
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t24 : ((-587207148003/5000000000000 : ℚ) : ℝ) ≤ stT262 24 := by
  have hc : ((-575343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-587207148003/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-575343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c25 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-305619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5571049/10000000) (δ := 3291/250000000) (ψ := -414889/500000) 262 134
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t25 : ((-152822076411/1250000000000 : ℚ) : ℝ) ≤ stT262 25 := by
  have hc : ((-76411/125000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152822076411/1250000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-76411/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c26 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((998071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -155319/10000000) (δ := 6589/500000000) (ψ := -414889/500000) 262 136
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t26 : ((1957279862381/10000000000000 : ℚ) : ℝ) ≤ stT262 26 := by
  have hc : ((998021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1957279862381/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((998021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c27 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-18413/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6851349/10000000) (δ := 1649/125000000) (ψ := -414889/500000) 262 138
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t27 : ((-17718880707/100000000000 : ℚ) : ℝ) ≤ stT262 27 := by
  have hc : ((-9207/10000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17718880707/100000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-9207/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c28 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((437681/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1261531/10000000) (δ := 819/62500000) (ψ := -414889/500000) 262 139
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t28 : ((51693246077/312500000000 : ℚ) : ℝ) ≤ stT262 28 := by
  have hc : ((54707/62500 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51693246077/312500000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((54707/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c29 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-962763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3584797/5000000) (δ := 6557/500000000) (ψ := -414889/500000) 262 141
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t29 : ((-893949725801/5000000000000 : ℚ) : ℝ) ≤ stT262 29 := by
  have hc : ((-962813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-893949725801/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-962813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c30 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((482041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -26883/400000) (δ := 6591/500000000) (ψ := -414889/500000) 262 142
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t30 : ((27501136683/156250000000 : ℚ) : ℝ) ≤ stT262 30 := by
  have hc : ((15063/15625 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27501136683/156250000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((15063/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c31 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-451229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2548673/5000000) (δ := 531/40000000) (ψ := -414889/500000) 262 143
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t31 : ((-405260726533/5000000000000 : ℚ) : ℝ) ≤ stT262 31 := by
  have hc : ((-451279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-405260726533/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-451279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c32 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-595973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2761591/5000000) (δ := 663/50000000) (ψ := -414889/500000) 262 145
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t32 : ((-1053629790641/10000000000000 : ℚ) : ℝ) ≤ stT262 32 := by
  have hc : ((-596023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1053629790641/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-596023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c33 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((908841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1075747/10000000) (δ := 13153/1000000000) (ψ := -414889/500000) 262 146
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t33 : ((197750195227/1250000000000 : ℚ) : ℝ) ≤ stT262 33 := by
  have hc : ((908791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197750195227/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((908791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c34 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((8929/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 554001/2000000) (δ := 13157/1000000000) (ψ := -414889/500000) 262 147
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t34 : ((95696163/1250000000 : ℚ) : ℝ) ≤ stT262 34 := by
  have hc : ((279/625 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95696163/1250000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((279/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c35 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-187613/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3024427/5000000) (δ := 13139/1000000000) (ψ := -414889/500000) 262 148
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t35 : ((-634290142559/5000000000000 : ℚ) : ℝ) ≤ stT262 35 := by
  have hc : ((-375251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-634290142559/5000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-375251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c36 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-93031/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6915133/10000000) (δ := 21/1600000) (ψ := -414889/500000) 262 150
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t36 : ((-38765007753/250000000000 : ℚ) : ℝ) ≤ stT262 36 := by
  have hc : ((-23259/25000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38765007753/250000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-23259/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c37 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-295429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4676751/10000000) (δ := 6593/500000000) (ψ := -414889/500000) 262 151
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t37 : ((-48576452121/1000000000000 : ℚ) : ℝ) ≤ stT262 37 := by
  have hc : ((-295479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48576452121/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-295479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c38 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((9827/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2917043/10000000) (δ := 13293/1000000000) (ψ := -414889/500000) 262 152
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t38 : ((31878938421/500000000000 : ℚ) : ℝ) ≤ stT262 38 := by
  have hc : ((39303/100000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31878938421/500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((39303/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c39 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((799447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -805527/5000000) (δ := 33/2500000) (ψ := -414889/500000) 262 153
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t39 : ((1280059227557/10000000000000 : ℚ) : ℝ) ≤ stT262 39 := by
  have hc : ((799397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1280059227557/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((799397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c40 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((956993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -735859/10000000) (δ := 831/62500000) (ψ := -414889/500000) 262 154
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t40 : ((756529470567/5000000000000 : ℚ) : ℝ) ≤ stT262 40 := by
  have hc : ((956943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((756529470567/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((956943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c41 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((497083/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -270169/10000000) (δ := 13189/1000000000) (ψ := -414889/500000) 262 155
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t41 : ((388136934873/2500000000000 : ℚ) : ℝ) ≤ stT262 41 := by
  have hc : ((248529/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((388136934873/2500000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((248529/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c42 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((124623/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48551/2500000) (δ := 6561/500000000) (ψ := -414889/500000) 262 156
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t42 : ((769151030411/5000000000000 : ℚ) : ℝ) ≤ stT262 42 := by
  have hc : ((498467/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((769151030411/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((498467/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c43 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((490439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48969/1000000) (δ := 6587/500000000) (ψ := -414889/500000) 262 157
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t43 : ((74787399379/500000000000 : ℚ) : ℝ) ≤ stT262 43 := by
  have hc : ((245207/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74787399379/500000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((245207/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c44 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((56119/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1139531/10000000) (δ := 13267/1000000000) (ψ := -414889/500000) 262 158
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t44 : ((169195648103/1250000000000 : ℚ) : ℝ) ≤ stT262 44 := by
  have hc : ((448927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169195648103/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((448927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c45 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((329569/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -212781/1000000) (δ := 329/25000000) (ψ := -414889/500000) 262 159
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t45 : ((61406858223/625000000000 : ℚ) : ℝ) ≤ stT262 45 := by
  have hc : ((41193/62500 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61406858223/625000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((41193/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c46 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((96863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1719797/5000000) (δ := 13253/1000000000) (ψ := -414889/500000) 262 160
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t46 : ((71389893561/2500000000000 : ℚ) : ℝ) ≤ stT262 46 := by
  have hc : ((48419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71389893561/2500000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((48419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c47 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-219091/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -506093/1000000) (δ := 13257/1000000000) (ψ := -414889/500000) 262 161
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t47 : ((-1598067767/25000000000 : ℚ) : ℝ) ≤ stT262 47 := by
  have hc : ((-54779/125000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1598067767/25000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-54779/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c48 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-234841/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6978917/10000000) (δ := 6619/500000000) (ψ := -414889/500000) 262 162
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t48 : ((-42372738177/312500000000 : ℚ) : ℝ) ≤ stT262 48 := by
  have hc : ((-469707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42372738177/312500000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-469707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c49 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-862337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6526659/10000000) (δ := 6619/500000000) (ψ := -414889/500000) 262 162
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t49 : ((-307995480341/2500000000000 : ℚ) : ℝ) ≤ stT262 49 := by
  have hc : ((-862387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-307995480341/2500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-862387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c50 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-9959/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 405153/1000000) (δ := 13131/1000000000) (ψ := -414889/500000) 262 163
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t50 : ((-7049149683/1000000000000 : ℚ) : ℝ) ≤ stT262 50 := by
  have hc : ((-9969/200000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7049149683/1000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-9969/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c51 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((864969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 131427/1000000) (δ := 13179/1000000000) (ψ := -414889/500000) 262 164
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t51 : ((30278219433/250000000000 : ℚ) : ℝ) ≤ stT262 51 := by
  have hc : ((864919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30278219433/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((864919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c52 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((391931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -837419/5000000) (δ := 13117/1000000000) (ψ := -414889/500000) 262 165
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t52 : ((1086951291/10000000000 : ℚ) : ℝ) ≤ stT262 52 := by
  have hc : ((195953/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1086951291/10000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((195953/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c53 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-95439/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -490623/1000000) (δ := 13193/1000000000) (ψ := -414889/500000) 262 166
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t53 : ((-131112753109/2500000000000 : ℚ) : ℝ) ≤ stT262 53 := by
  have hc : ((-190903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131112753109/2500000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-190903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c54 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-489351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1467419/2000000) (δ := 1321/100000000) (ψ := -414889/500000) 262 166
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t54 : ((-5202785651/39062500000 : ℚ) : ℝ) ≤ stT262 54 := by
  have hc : ((-15293/15625 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5202785651/39062500000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-15293/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c55 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((111447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3647793/10000000) (δ := 133/10000000) (ψ := -414889/500000) 262 167
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t55 : ((150207603403/10000000000000 : ℚ) : ℝ) ≤ stT262 55 := by
  have hc : ((111397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150207603403/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((111397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c56 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((994677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -258053/10000000) (δ := 1651/125000000) (ψ := -414889/500000) 262 168
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t56 : ((664563013931/5000000000000 : ℚ) : ℝ) ≤ stT262 56 := by
  have hc : ((994627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((664563013931/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((994627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c57 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-44343/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4372779/10000000) (δ := 1661/125000000) (ψ := -414889/500000) 262 169
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t57 : ((-117500646963/5000000000000 : ℚ) : ℝ) ≤ stT262 57 := by
  have hc : ((-88711/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117500646963/5000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-88711/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c58 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-944721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 140377/200000) (δ := 1661/125000000) (ψ := -414889/500000) 262 169
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t58 : ((-248109146623/2000000000000 : ℚ) : ℝ) ≤ stT262 58 := by
  have hc : ((-944771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-248109146623/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-944771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c59 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((268851/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2507719/10000000) (δ := 13181/1000000000) (ψ := -414889/500000) 262 170
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t59 : ((174990806157/2500000000000 : ℚ) : ℝ) ≤ stT262 59 := by
  have hc : ((134413/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174990806157/2500000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((134413/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c60 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((639739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1095797/5000000) (δ := 6637/500000000) (ψ := -414889/500000) 262 171
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t60 : ((412917330433/5000000000000 : ℚ) : ℝ) ≤ stT262 60 := by
  have hc : ((639689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((412917330433/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((639689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c61 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-29737/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1414573/2000000) (δ := 3309/250000000) (ψ := -414889/500000) 262 172
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t61 : ((-609221336473/5000000000000 : ℚ) : ℝ) ≤ stT262 61 := by
  have hc : ((-475817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-609221336473/5000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-475817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c62 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((69619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1788881/5000000) (δ := 13167/1000000000) (ψ := -414889/500000) 262 172
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t62 : ((44192224797/2500000000000 : ℚ) : ℝ) ≤ stT262 62 := by
  have hc : ((34797/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44192224797/2500000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((34797/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c63 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((790007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1649939/10000000) (δ := 1643/125000000) (ψ := -414889/500000) 262 173
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t63 : ((995251815117/10000000000000 : ℚ) : ℝ) ≤ stT262 63 := by
  have hc : ((789957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((995251815117/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((789957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c64 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-189563/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3521383/5000000) (δ := 411/31250000) (ψ := -414889/500000) 262 174
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t64 : ((-236966439573/2000000000000 : ℚ) : ℝ) ≤ stT262 64 := by
  have hc : ((-189573/200000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236966439573/2000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-189573/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c65 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((320069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 622497/2000000) (δ := 411/31250000) (ψ := -414889/500000) 262 174
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t65 : ((396934606593/10000000000000 : ℚ) : ℝ) ≤ stT262 65 := by
  have hc : ((320019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((396934606593/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((320019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c66 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((126963/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1297633/5000000) (δ := 2649/200000000) (ψ := -414889/500000) 262 175
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t66 : ((156265147757/2500000000000 : ℚ) : ℝ) ≤ stT262 66 := by
  have hc : ((253901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156265147757/2500000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((253901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c67 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-971393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7254559/10000000) (δ := 6579/500000000) (ψ := -414889/500000) 262 175
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t67 : ((-237361411177/2000000000000 : ℚ) : ℝ) ≤ stT262 67 := by
  have hc : ((-971443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237361411177/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-971443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c68 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((877489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 625243/5000000) (δ := 6569/500000000) (ψ := -414889/500000) 262 176
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t68 : ((532025485821/5000000000000 : ℚ) : ℝ) ≤ stT262 68 := by
  have hc : ((877439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((532025485821/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((877439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c69 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-188849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4895263/10000000) (δ := 3293/250000000) (ψ := -414889/500000) 262 177
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t69 : ((-113688832383/2500000000000 : ℚ) : ℝ) ≤ stT262 69 := by
  have hc : ((-94437/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113688832383/2500000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-94437/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c70 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-238613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 905867/2000000) (δ := 13231/1000000000) (ψ := -414889/500000) 262 177
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t70 : ((-285256938827/10000000000000 : ℚ) : ℝ) ≤ stT262 70 := by
  have hc : ((-238663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285256938827/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-238663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c71 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((728213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -377543/2000000) (δ := 3281/250000000) (ψ := -414889/500000) 262 178
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t71 : ((864170013303/10000000000000 : ℚ) : ℝ) ≤ stT262 71 := by
  have hc : ((728163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((864170013303/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((728163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c72 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-973147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 227291/312500) (δ := 13279/1000000000) (ψ := -414889/500000) 262 178
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t72 : ((-71682771429/625000000000 : ℚ) : ℝ) ≤ stT262 72 := by
  have hc : ((-973197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71682771429/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-973197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c73 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((485671/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14999/250000) (δ := 13187/1000000000) (ψ := -414889/500000) 262 179
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t73 : ((284202710253/2500000000000 : ℚ) : ℝ) ≤ stT262 73 := by
  have hc : ((242823/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((284202710253/2500000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((242823/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c74 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-788113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1239267/2000000) (δ := 6647/500000000) (ψ := -414889/500000) 262 180
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t74 : ((-916221359751/10000000000000 : ℚ) : ℝ) ≤ stT262 74 := by
  have hc : ((-788163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-916221359751/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-788163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c75 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((50767/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 519159/2000000) (δ := 13109/1000000000) (ψ := -414889/500000) 262 180
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t75 : ((293074407/5000000000 : ℚ) : ℝ) ≤ stT262 75 := by
  have hc : ((25381/50000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((293074407/5000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((25381/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c76 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-10121/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2218281/5000000) (δ := 13201/1000000000) (ψ := -414889/500000) 262 181
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t76 : ((-23224908513/1000000000000 : ℚ) : ℝ) ≤ stT262 76 := by
  have hc : ((-20247/100000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23224908513/1000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-20247/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c77 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-15877/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4125663/10000000) (δ := 6601/500000000) (ψ := -414889/500000) 262 181
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t77 : ((-9052460261/1000000000000 : ℚ) : ℝ) ≤ stT262 77 := by
  have hc : ((-15887/200000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9052460261/1000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-15887/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c78 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((156603/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3130573/10000000) (δ := 3277/250000000) (ψ := -414889/500000) 262 182
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t78 : ((88644834053/2500000000000 : ℚ) : ℝ) ≤ stT262 78 := by
  have hc : ((78289/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88644834053/2500000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((78289/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c79 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-24609/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 162921/312500) (δ := 3277/250000000) (ψ := -414889/500000) 262 182
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t79 : ((-1730631457/31250000000 : ℚ) : ℝ) ≤ stT262 79 := by
  have hc : ((-49223/100000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1730631457/31250000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-49223/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c80 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((154981/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2255377/10000000) (δ := 2643/200000000) (ψ := -414889/500000) 262 183
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t80 : ((346519793921/5000000000000 : ℚ) : ℝ) ≤ stT262 80 := by
  have hc : ((309937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((346519793921/5000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((309937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c81 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-704521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73517/125000) (δ := 3297/250000000) (ψ := -414889/500000) 262 183
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t81 : ((-97857161619/1250000000000 : ℚ) : ℝ) ≤ stT262 81 := by
  have hc : ((-704571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97857161619/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-704571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c82 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((754519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -223711/1250000) (δ := 83/6250000) (ψ := -414889/500000) 262 184
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t82 : ((166634286747/2000000000000 : ℚ) : ℝ) ≤ stT262 82 := by
  have hc : ((754469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166634286747/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((754469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c83 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-776527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6149829/10000000) (δ := 83/6250000) (ψ := -414889/500000) 262 184
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t83 : ((-852404308011/10000000000000 : ℚ) : ℝ) ≤ stT262 83 := by
  have hc : ((-776577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-852404308011/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-776577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c84 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((774101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -428439/2500000) (δ := 26373/1000000000) (ψ := -414889/500000) 262 185
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t84 : ((844558531539/10000000000000 : ℚ) : ℝ) ≤ stT262 84 := by
  have hc : ((774051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((844558531539/10000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((774051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c85 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-186881/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6037809/10000000) (δ := 13173/1000000000) (ψ := -414889/500000) 262 185
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t85 : ((-405429190911/5000000000000 : ℚ) : ℝ) ≤ stT262 85 := by
  have hc : ((-373787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-405429190911/5000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-373787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c86 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((694041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1004637/5000000) (δ := 13137/1000000000) (ψ := -414889/500000) 262 186
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t86 : ((748349233057/10000000000000 : ℚ) : ℝ) ≤ stT262 86 := by
  have hc : ((693991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((748349233057/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((693991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c87 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-608723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1112623/2000000) (δ := 6633/500000000) (ψ := -414889/500000) 262 186
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t87 : ((-652673447349/10000000000000 : ℚ) : ℝ) ≤ stT262 87 := by
  have hc : ((-608773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-652673447349/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-608773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c88 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((485711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2659049/10000000) (δ := 3311/250000000) (ψ := -414889/500000) 262 187
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t88 : ((517716082983/10000000000000 : ℚ) : ℝ) ≤ stT262 88 := by
  have hc : ((485661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((517716082983/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((485661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c89 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-160153/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4742123/10000000) (δ := 13159/1000000000) (ψ := -414889/500000) 262 187
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t89 : ((-42447089911/1250000000000 : ℚ) : ℝ) ≤ stT262 89 := by
  have hc : ((-80089/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42447089911/1250000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-80089/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c90 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((6977/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3647329/10000000) (δ := 3313/250000000) (ψ := -414889/500000) 262 188
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t90 : ((14702211693/1250000000000 : ℚ) : ℝ) ≤ stT262 90 := by
  have hc : ((55791/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14702211693/1250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((55791/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c91 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((6713/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3590323/10000000) (δ := 6563/250000000) (ψ := -414889/500000) 262 188
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t91 : ((3517254891/250000000000 : ℚ) : ℝ) ≤ stT262 91 := by
  have hc : ((13421/100000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3517254891/250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((13421/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c92 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-20061/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -619889/1250000) (δ := 6629/500000000) (ψ := -414889/500000) 262 189
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t92 : ((-41835326771/1000000000000 : ℚ) : ℝ) ≤ stT262 92 := by
  have hc : ((-40127/100000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41835326771/1000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-40127/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c93 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((165219/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2122027/10000000) (δ := 2629/200000000) (ψ := -414889/500000) 262 189
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t93 : ((342622090763/5000000000000 : ℚ) : ℝ) ≤ stT262 93 := by
  have hc : ((330413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((342622090763/5000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((330413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c94 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-218261/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1316103/2000000) (δ := 13237/1000000000) (ψ := -414889/500000) 262 190
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t94 : ((-225132089917/2500000000000 : ℚ) : ℝ) ≤ stT262 94 := by
  have hc : ((-436547/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225132089917/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-436547/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c95 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((990173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 350761/10000000) (δ := 6583/500000000) (ψ := -414889/500000) 262 190
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t95 : ((507922207647/5000000000000 : ℚ) : ℝ) ≤ stT262 95 := by
  have hc : ((990123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((507922207647/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((990123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c96 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-966951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3604731/5000000) (δ := 13237/1000000000) (ψ := -414889/500000) 262 190
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t96 : ((-986941527621/10000000000000 : ℚ) : ℝ) ≤ stT262 96 := by
  have hc : ((-967001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-986941527621/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-967001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c97 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((48427/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1710867/10000000) (δ := 1313/100000000) (ψ := -414889/500000) 262 191
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t97 : ((196667951143/2500000000000 : ℚ) : ℝ) ≤ stT262 97 := by
  have hc : ((387391/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196667951143/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((387391/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c98 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-209371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5007141/10000000) (δ := 13273/1000000000) (ψ := -414889/500000) 262 191
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t98 : ((-52880499397/1250000000000 : ℚ) : ℝ) ≤ stT262 98 := by
  have hc : ((-52349/125000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52880499397/1250000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-52349/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c99 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-3099/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4051001/10000000) (δ := 13223/1000000000) (ψ := -414889/500000) 262 192
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t99 : ((-12471014023/2500000000000 : ℚ) : ℝ) ≤ stT262 99 := by
  have hc : ((-24817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12471014023/2500000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-24817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c100 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((264753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1265973/5000000) (δ := 659/50000000) (ψ := -414889/500000) 262 192
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t100 : ((33090966909/625000000000 : ℚ) : ℝ) ≤ stT262 100 := by
  have hc : ((33091/62500 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33090966909/625000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((33091/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c101 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-887829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1331701/2000000) (δ := 13287/1000000000) (ψ := -414889/500000) 262 193
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t101 : ((-441736672201/5000000000000 : ℚ) : ℝ) ≤ stT262 101 := by
  have hc : ((-887879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-441736672201/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-887879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c102 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((124579/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -205249/10000000) (δ := 3279/250000000) (ψ := -414889/500000) 262 193
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t102 : ((493381338777/5000000000000 : ℚ) : ℝ) ≤ stT262 102 := by
  have hc : ((498291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((493381338777/5000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((498291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c103 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-392657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6184997/10000000) (δ := 13287/1000000000) (ψ := -414889/500000) 262 193
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t103 : ((-19346067753/250000000000 : ℚ) : ℝ) ≤ stT262 103 := by
  have hc : ((-196341/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19346067753/250000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-196341/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c104 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((72213/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1597211/5000000) (δ := 6597/500000000) (ψ := -414889/500000) 262 194
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t104 : ((7079836629/250000000000 : ℚ) : ℝ) ≤ stT262 104 := by
  have hc : ((144401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7079836629/250000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((144401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c105 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((66953/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1921/6250) (δ := 13209/1000000000) (ψ := -414889/500000) 262 194
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t105 : ((653296737/20000000000 : ℚ) : ℝ) ≤ stT262 105 := by
  have hc : ((66943/200000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((653296737/20000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((66943/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c106 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-841217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1285163/2000000) (δ := 13301/1000000000) (ψ := -414889/500000) 262 195
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t106 : ((-408555429681/5000000000000 : ℚ) : ℝ) ≤ stT262 106 := by
  have hc : ((-841267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-408555429681/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-841267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c107 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((496967/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -34437/1250000) (δ := 13301/1000000000) (ψ := -414889/500000) 262 195
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t107 : ((15012866291/156250000000 : ℚ) : ℝ) ≤ stT262 107 := by
  have hc : ((248471/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15012866291/156250000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((248471/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c108 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-686187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 727197/1250000) (δ := 13301/1000000000) (ψ := -414889/500000) 262 195
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t108 : ((-660332239487/10000000000000 : ℚ) : ℝ) ≤ stT262 108 := by
  have hc : ((-686237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-660332239487/10000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-686237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c109 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((14693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1926757/5000000) (δ := 6597/500000000) (ψ := -414889/500000) 262 196
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t109 : ((1756173971/625000000000 : ℚ) : ℝ) ≤ stT262 109 := by
  have hc : ((3667/125000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1756173971/625000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((3667/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c110 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((658999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1064137/5000000) (δ := 13209/1000000000) (ψ := -414889/500000) 262 196
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t110 : ((314141415719/5000000000000 : ℚ) : ℝ) ≤ stT262 110 := by
  have hc : ((658949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((314141415719/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((658949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c111 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-498369/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1530401/2000000) (δ := 3279/250000000) (ψ := -414889/500000) 262 197
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t111 : ((-118263663063/1250000000000 : ℚ) : ℝ) ≤ stT262 111 := by
  have hc : ((-249197/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118263663063/1250000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-249197/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c112 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((757691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -444393/2500000) (δ := 3279/250000000) (ψ := -414889/500000) 262 197
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t112 : ((715903314951/10000000000000 : ℚ) : ℝ) ≤ stT262 112 := by
  have hc : ((757641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((715903314951/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((757641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c113 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-1883/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4044723/10000000) (δ := 3279/250000000) (ψ := -414889/500000) 262 197
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t113 : ((-354651817/80000000000 : ℚ) : ℝ) ≤ stT262 113 := by
  have hc : ((-377/8000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-354651817/80000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-377/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c114 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-707619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5892297/10000000) (δ := 13223/1000000000) (ψ := -414889/500000) 262 198
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t114 : ((-331396439017/5000000000000 : ℚ) : ℝ) ≤ stT262 114 := by
  have hc : ((-707669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-331396439017/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-707669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c115 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((498821/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42931/2500000) (δ := 659/50000000) (ψ := -414889/500000) 262 198
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t115 : ((14535289537/156250000000 : ℚ) : ℝ) ≤ stT262 115 := by
  have hc : ((124699/125000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14535289537/156250000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((124699/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c116 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-73533/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2749633/5000000) (δ := 659/50000000) (ψ := -414889/500000) 262 198
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t116 : ((-273118008889/5000000000000 : ℚ) : ℝ) ≤ stT262 116 := by
  have hc : ((-294157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-273118008889/5000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-294157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c117 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-6517/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1146577/2500000) (δ := 1313/100000000) (ψ := -414889/500000) 262 199
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t117 : ((-24104514573/1000000000000 : ℚ) : ℝ) ≤ stT262 117 := by
  have hc : ((-26073/100000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24104514573/1000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-26073/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c118 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((922889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4941/50000) (δ := 13273/1000000000) (ψ := -414889/500000) 262 199
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t118 : ((424770794793/5000000000000 : ℚ) : ℝ) ≤ stT262 118 := by
  have hc : ((922839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((424770794793/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((922839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c119 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-215023/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3257807/5000000) (δ := 13273/1000000000) (ψ := -414889/500000) 262 199
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t119 : ((-394245655629/5000000000000 : ℚ) : ℝ) ≤ stT262 119 := by
  have hc : ((-430071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-394245655629/5000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-430071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c120 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((21561/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -463889/1250000) (δ := 13237/1000000000) (ψ := -414889/500000) 262 200
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t120 : ((3934195839/500000000000 : ℚ) : ℝ) ≤ stT262 120 := by
  have hc : ((43097/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3934195839/500000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((43097/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c121 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((771347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 862301/5000000) (δ := 13237/1000000000) (ψ := -414889/500000) 262 200
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t121 : ((70117838973/1000000000000 : ℚ) : ℝ) ≤ stT262 121 := by
  have hc : ((771297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70117838973/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((771297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c122 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-956697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7115579/10000000) (δ := 6583/500000000) (ψ := -414889/500000) 262 200
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t122 : ((-433099275213/5000000000000 : ℚ) : ℝ) ≤ stT262 122 := by
  have hc : ((-956747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-433099275213/5000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-956747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c123 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((134631/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3245423/10000000) (δ := 6629/500000000) (ψ := -414889/500000) 262 201
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t123 : ((60685028707/2500000000000 : ℚ) : ℝ) ≤ stT262 123 := by
  have hc : ((67303/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60685028707/2500000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((67303/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c124 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((679807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2058243/10000000) (δ := 6629/500000000) (ψ := -414889/500000) 262 201
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t124 : ((305219729841/5000000000000 : ℚ) : ℝ) ≤ stT262 124 := by
  have hc : ((679757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((305219729841/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((679757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c125 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-977219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3659667/5000000) (δ := 6629/500000000) (ψ := -414889/500000) 262 201
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t125 : ((-218524189283/2500000000000 : ℚ) : ℝ) ≤ stT262 125 := by
  have hc : ((-977269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218524189283/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-977269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c126 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((298397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1584729/5000000) (δ := 13151/1000000000) (ψ := -414889/500000) 262 202
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t126 : ((26578839189/1000000000000 : ℚ) : ℝ) ≤ stT262 126 := by
  have hc : ((298347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26578839189/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((298347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c127 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((694297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2008383/10000000) (δ := 3313/250000000) (ψ := -414889/500000) 262 202
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t127 : ((154011060233/2500000000000 : ℚ) : ℝ) ≤ stT262 127 := by
  have hc : ((694247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154011060233/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((694247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c128 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-240033/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7145679/10000000) (δ := 3313/250000000) (ψ := -414889/500000) 262 202
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t128 : ((-106086188361/1250000000000 : ℚ) : ℝ) ≤ stT262 128 := by
  have hc : ((-480091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106086188361/1250000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-480091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c129 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((22971/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -216559/625000) (δ := 3311/250000000) (ψ := -414889/500000) 262 203
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t129 : ((1617545131/100000000000 : ℚ) : ℝ) ≤ stT262 129 := by
  have hc : ((91859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1617545131/100000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((91859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c130 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((803773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 796483/5000000) (δ := 3311/250000000) (ψ := -414889/500000) 262 203
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t130 : ((352455843467/5000000000000 : ℚ) : ℝ) ≤ stT262 130 := by
  have hc : ((803723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352455843467/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((803723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c131 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-879147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3306083/5000000) (δ := 13159/1000000000) (ψ := -414889/500000) 262 203
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t131 : ((-153631762977/2000000000000 : ℚ) : ℝ) ≤ stT262 131 := by
  have hc : ((-879197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153631762977/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-879197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c132 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-75047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -128587/312500) (δ := 6633/500000000) (ψ := -414889/500000) 262 204
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t132 : ((-65363602733/10000000000000 : ℚ) : ℝ) ≤ stT262 132 := by
  have hc : ((-75097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65363602733/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-75097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c133 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((945571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 103579/1250000) (δ := 6633/500000000) (ψ := -414889/500000) 262 204
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t133 : ((819869768789/10000000000000 : ℚ) : ℝ) ≤ stT262 133 := by
  have hc : ((945521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((819869768789/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((945521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c134 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-20681/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5735007/10000000) (δ := 26337/1000000000) (ψ := -414889/500000) 262 204
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t134 : ((-285872393349/5000000000000 : ℚ) : ℝ) ≤ stT262 134 := by
  have hc : ((-330921/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285872393349/5000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-330921/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c135 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-453269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -637883/1250000) (δ := 1323/100000000) (ψ := -414889/500000) 262 205
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t135 : ((-390154890497/10000000000000 : ℚ) : ℝ) ≤ stT262 135 := by
  have hc : ((-453319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-390154890497/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-453319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c136 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((248553/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -134549/5000000) (δ := 13173/1000000000) (ψ := -414889/500000) 262 205
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t136 : ((106560745213/1250000000000 : ℚ) : ℝ) ≤ stT262 136 := by
  have hc : ((497081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106560745213/1250000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((497081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c137 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-59669/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4529497/10000000) (δ := 1323/100000000) (ψ := -414889/500000) 262 205
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t137 : ((-50989366977/2500000000000 : ℚ) : ℝ) ≤ stT262 137 := by
  have hc : ((-119363/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50989366977/2500000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-119363/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c138 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-838837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6414847/10000000) (δ := 83/6250000) (ψ := -414889/500000) 262 206
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t138 : ((-714108430959/10000000000000 : ℚ) : ℝ) ≤ stT262 138 := by
  have hc : ((-838887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-714108430959/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-838887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c139 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((390597/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1685551/10000000) (δ := 13123/1000000000) (ψ := -414889/500000) 262 206
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t139 : ((20704905221/312500000000 : ℚ) : ℝ) ≤ stT262 139 := by
  have hc : ((97643/125000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20704905221/312500000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((97643/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c140 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((71739/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3009817/10000000) (δ := 83/6250000) (ψ := -414889/500000) 262 206
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t140 : ((30311025633/1000000000000 : ℚ) : ℝ) ≤ stT262 140 := by
  have hc : ((71729/200000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30311025633/1000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((71729/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c141 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-997343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3835857/5000000) (δ := 83/6250000) (ψ := -414889/500000) 262 206
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t141 : ((-104994563717/1250000000000 : ℚ) : ℝ) ≤ stT262 141 := by
  have hc : ((-997393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104994563717/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-997393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c142 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((25801/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1703617/5000000) (δ := 2643/200000000) (ψ := -414889/500000) 262 207
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t142 : ((86585856399/5000000000000 : ℚ) : ℝ) ≤ stT262 142 := by
  have hc : ((103179/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86585856399/5000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((103179/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c143 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((222241/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 594647/5000000) (δ := 2643/200000000) (ψ := -414889/500000) 262 207
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t143 : ((185836805297/2500000000000 : ℚ) : ℝ) ≤ stT262 143 := by
  have hc : ((444457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185836805297/2500000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((444457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c144 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-667387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5753727/10000000) (δ := 2643/200000000) (ψ := -414889/500000) 262 207
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t144 : ((-278098972479/5000000000000 : ℚ) : ℝ) ≤ stT262 144 := by
  have hc : ((-667437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278098972479/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-667437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c145 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-112553/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1355327/2500000) (δ := 2659/200000000) (ψ := -414889/500000) 262 208
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t145 : ((-18695701233/400000000000 : ℚ) : ℝ) ≤ stT262 145 := by
  have hc : ((-112563/200000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18695701233/400000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-112563/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c146 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((116639/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -919559/10000000) (δ := 3277/250000000) (ψ := -414889/500000) 262 208
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t146 : ((77220677651/1000000000000 : ℚ) : ℝ) ≤ stT262 146 := by
  have hc : ((466531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77220677651/1000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((466531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c147 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((149669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1775703/5000000) (δ := 2659/200000000) (ψ := -414889/500000) 262 208
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t147 : ((61701828267/5000000000000 : ℚ) : ℝ) ≤ stT262 147 := by
  have hc : ((149619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61701828267/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((149619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c148 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-499237/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3857927/5000000) (δ := 6601/500000000) (ψ := -414889/500000) 262 209
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t148 : ((-41039086769/500000000000 : ℚ) : ℝ) ≤ stT262 148 := by
  have hc : ((-249631/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41039086769/500000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-249631/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c149 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((24623/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3305019/10000000) (δ := 13201/1000000000) (ψ := -414889/500000) 262 209
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t149 : ((10083914379/500000000000 : ℚ) : ℝ) ≤ stT262 149 := by
  have hc : ((12309/50000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10083914379/500000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((12309/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c150 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((227191/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1076211/10000000) (δ := 6601/500000000) (ψ := -414889/500000) 262 209
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t150 : ((23186292067/312500000000 : ℚ) : ℝ) ≤ stT262 150 := by
  have hc : ((454357/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23186292067/312500000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((454357/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c151 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-141279/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 678553/1250000) (δ := 6601/500000000) (ψ := -414889/500000) 262 209
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t151 : ((-229962936987/5000000000000 : ℚ) : ℝ) ≤ stT262 151 := by
  have hc : ((-282583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229962936987/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-282583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c152 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-362707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5956081/10000000) (δ := 13109/1000000000) (ψ := -414889/500000) 262 210
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t152 : ((-18388426691/312500000000 : ℚ) : ℝ) ≤ stT262 152 := by
  have hc : ((-90683/125000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18388426691/312500000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-90683/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c153 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((787291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -207623/1250000) (δ := 13109/1000000000) (ψ := -414889/500000) 262 210
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t153 : ((159111640233/2500000000000 : ℚ) : ℝ) ≤ stT262 153 := by
  have hc : ((787241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159111640233/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((787241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c154 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((504099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40721/156250) (δ := 6647/500000000) (ψ := -414889/500000) 262 210
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t154 : ((203086886639/5000000000000 : ℚ) : ℝ) ≤ stT262 154 := by
  have hc : ((504049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203086886639/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((504049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c155 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-183951/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 106963/156250) (δ := 13109/1000000000) (ψ := -414889/500000) 262 210
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t155 : ((-7388057721/100000000000 : ℚ) : ℝ) ≤ stT262 155 := by
  have hc : ((-183961/200000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7388057721/100000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-183961/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c156 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-35653/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1162523/2500000) (δ := 13187/1000000000) (ψ := -414889/500000) 262 211
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t156 : ((-114201030317/5000000000000 : ℚ) : ℝ) ≤ stT262 156 := by
  have hc : ((-142637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114201030317/5000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-142637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c157 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((982769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -464773/10000000) (δ := 13187/1000000000) (ψ := -414889/500000) 262 211
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t157 : ((392147137917/5000000000000 : ℚ) : ℝ) ≤ stT262 157 := by
  have hc : ((982719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((392147137917/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((982719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c158 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((2327/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3693953/10000000) (δ := 13187/1000000000) (ψ := -414889/500000) 262 211
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t158 : ((7401066771/1000000000000 : ℚ) : ℝ) ≤ stT262 158 := by
  have hc : ((9303/100000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7401066771/1000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((9303/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c159 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-999939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7826479/10000000) (δ := 13187/1000000000) (ψ := -414889/500000) 262 211
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t159 : ((-198260819107/2500000000000 : ℚ) : ℝ) ≤ stT262 159 := by
  have hc : ((-999989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198260819107/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-999989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c160 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((38/625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -235931/625000) (δ := 3281/250000000) (ψ := -414889/500000) 262 212
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t160 : ((192108267/40000000000 : ℚ) : ℝ) ≤ stT262 160 := by
  have hc : ((243/4000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192108267/40000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((243/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c161 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((198503/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 306081/10000000) (δ := 13279/1000000000) (ψ := -414889/500000) 262 212
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t161 : ((15643431823/200000000000 : ℚ) : ℝ) ≤ stT262 161 := by
  have hc : ((198493/200000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15643431823/200000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((198493/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c162 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-21633/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4361841/10000000) (δ := 13279/1000000000) (ψ := -414889/500000) 262 212
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t162 : ((-2720226839/200000000000 : ℚ) : ℝ) ≤ stT262 162 := by
  have hc : ((-86557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2720226839/200000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-86557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c163 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-976877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7315317/10000000) (δ := 13231/1000000000) (ψ := -414889/500000) 262 213
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t163 : ((-765188818947/10000000000000 : ℚ) : ℝ) ≤ stT262 163 := by
  have hc : ((-976927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-765188818947/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-976927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c164 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((244607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1654603/5000000) (δ := 13231/1000000000) (ψ := -414889/500000) 262 213
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t164 : ((47741683869/2500000000000 : ℚ) : ℝ) ≤ stT262 164 := by
  have hc : ((244557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47741683869/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((244557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c165 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((964033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 672539/10000000) (δ := 13231/1000000000) (ψ := -414889/500000) 262 213
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t165 : ((375229418767/5000000000000 : ℚ) : ℝ) ≤ stT262 165 := by
  have hc : ((963983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((375229418767/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((963983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c166 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-138803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 926049/2000000) (δ := 3293/250000000) (ψ := -414889/500000) 262 213
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t166 : ((-26937872757/1250000000000 : ℚ) : ℝ) ≤ stT262 166 := by
  have hc : ((-34707/125000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26937872757/1250000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-34707/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c167 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-959913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7143723/10000000) (δ := 2653/200000000) (ψ := -414889/500000) 262 214
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t167 : ((-11606912633/156250000000 : ℚ) : ℝ) ≤ stT262 167 := by
  have hc : ((-959963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11606912633/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-959963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c168 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((273927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3233307/10000000) (δ := 6569/500000000) (ψ := -414889/500000) 262 214
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t168 : ((52825121883/2500000000000 : ℚ) : ℝ) ≤ stT262 168 := by
  have hc : ((273877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52825121883/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((273877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c169 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((965979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 653987/10000000) (δ := 6569/500000000) (ψ := -414889/500000) 262 214
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t169 : ((74302156467/1000000000000 : ℚ) : ℝ) ≤ stT262 169 := by
  have hc : ((965929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74302156467/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((965929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c170 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-234321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 451829/1000000) (δ := 2653/200000000) (ψ := -414889/500000) 262 214
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t170 : ((-35950870803/2000000000000 : ℚ) : ℝ) ≤ stT262 170 := by
  have hc : ((-234371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35950870803/2000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-234371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c171 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-979591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -114813/156250) (δ := 2649/200000000) (ψ := -414889/500000) 262 215
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t171 : ((-9364388319/125000000000 : ℚ) : ℝ) ≤ stT262 171 := by
  have hc : ((-979641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9364388319/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-979641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c172 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((79303/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3528793/10000000) (δ := 6579/500000000) (ψ := -414889/500000) 262 215
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t172 : ((7556105097/625000000000 : ℚ) : ℝ) ≤ stT262 172 := by
  have hc : ((39639/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7556105097/625000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((39639/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c173 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((497123/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 67077/2500000) (δ := 2649/200000000) (ψ := -414889/500000) 262 215
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t173 : ((37793615293/500000000000 : ℚ) : ℝ) ≤ stT262 173 := by
  have hc : ((248549/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37793615293/500000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((248549/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c174 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-46599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4043531/10000000) (δ := 6579/500000000) (ψ := -414889/500000) 262 215
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t174 : ((-35364560251/10000000000000 : ℚ) : ℝ) ≤ stT262 174 := by
  have hc : ((-46649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35364560251/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-46649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c175 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-499871/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 389857/500000) (δ := 2649/200000000) (ψ := -414889/500000) 262 215
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t175 : ((-47235735423/625000000000 : ℚ) : ℝ) ≤ stT262 175 := by
  have hc : ((-62487/62500 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47235735423/625000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-62487/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c176 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-100487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2089317/5000000) (δ := 13251/1000000000) (ψ := -414889/500000) 262 216
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t176 : ((-75782679323/10000000000000 : ℚ) : ℝ) ≤ stT262 176 := by
  have hc : ((-100537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75782679323/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-100537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c177 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((245641/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -93507/2000000) (δ := 13251/1000000000) (ψ := -414889/500000) 262 216
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t177 : ((184625679511/2500000000000 : ℚ) : ℝ) ≤ stT262 177 := by
  have hc : ((491257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184625679511/2500000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((491257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c178 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((139021/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 805651/2500000) (δ := 13251/1000000000) (ψ := -414889/500000) 262 216
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t178 : ((26045452719/1250000000000 : ℚ) : ℝ) ≤ stT262 178 := by
  have hc : ((34749/125000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26045452719/1250000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((34749/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c179 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-926893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6892111/10000000) (δ := 411/31250000) (ψ := -414889/500000) 262 216
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t179 : ((-173207642037/2500000000000 : ℚ) : ℝ) ≤ stT262 179 := by
  have hc : ((-926943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173207642037/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-926943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c180 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-475861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5166847/10000000) (δ := 13259/1000000000) (ψ := -414889/500000) 262 217
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t180 : ((-88680779829/2500000000000 : ℚ) : ℝ) ≤ stT262 180 := by
  have hc : ((-475911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88680779829/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-475911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c181 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((408327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48063/312500) (δ := 13259/1000000000) (ψ := -414889/500000) 262 217
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t181 : ((75872106697/1250000000000 : ℚ) : ℝ) ≤ stT262 181 := by
  have hc : ((204151/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75872106697/1250000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((204151/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c182 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((676123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 517693/2500000) (δ := 13259/1000000000) (ψ := -414889/500000) 262 217
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t182 : ((501138435177/10000000000000 : ℚ) : ℝ) ≤ stT262 182 := by
  have hc : ((676073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((501138435177/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((676073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c183 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-638957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1414961/2500000) (δ := 1643/125000000) (ψ := -414889/500000) 262 217
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t183 : ((-236184016277/5000000000000 : ℚ) : ℝ) ≤ stT262 183 := by
  have hc : ((-639007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236184016277/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-639007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c184 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-852451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6478631/10000000) (δ := 13167/1000000000) (ψ := -414889/500000) 262 218
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t184 : ((-62847226221/1000000000000 : ℚ) : ℝ) ≤ stT262 184 := by
  have hc : ((-852501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62847226221/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-852501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c185 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((3111/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1464233/5000000) (δ := 3309/250000000) (ψ := -414889/500000) 262 218
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t185 : ((5717391671/200000000000 : ℚ) : ℝ) ≤ stT262 185 := by
  have hc : ((15553/40000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5717391671/200000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((15553/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c186 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((971099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 150627/2500000) (δ := 3309/250000000) (ψ := -414889/500000) 262 218
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t186 : ((142401422703/2000000000000 : ℚ) : ℝ) ≤ stT262 186 := by
  have hc : ((971049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142401422703/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((971049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c187 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-3749/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2057309/5000000) (δ := 3309/250000000) (ψ := -414889/500000) 262 218
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t187 : ((-5486741319/1000000000000 : ℚ) : ℝ) ≤ stT262 187 := by
  have hc : ((-7503/100000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5486741319/1000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-7503/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c188 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-995161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 760793/1000000) (δ := 13167/1000000000) (ψ := -414889/500000) 262 218
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t188 : ((-29033290503/400000000000 : ℚ) : ℝ) ≤ stT262 188 := by
  have hc : ((-995211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29033290503/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-995211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c189 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-17229/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4625193/10000000) (δ := 13129/1000000000) (ψ := -414889/500000) 262 219
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t189 : ((-100276216801/5000000000000 : ℚ) : ℝ) ≤ stT262 189 := by
  have hc : ((-137857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100276216801/5000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-137857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c190 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((111587/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -584379/5000000) (δ := 13129/1000000000) (ψ := -414889/500000) 262 219
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t190 : ((80949156187/1250000000000 : ℚ) : ℝ) ≤ stT262 190 := by
  have hc : ((446323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80949156187/1250000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((446323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c191 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((12309/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2269599/10000000) (δ := 13129/1000000000) (ψ := -414889/500000) 262 219
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t191 : ((1113218599/25000000000 : ℚ) : ℝ) ≤ stT262 191 := by
  have hc : ((3077/5000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1113218599/25000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((3077/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c192 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-162043/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 711243/1250000) (δ := 6637/500000000) (ψ := -414889/500000) 262 219
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t192 : ((-29238377421/625000000000 : ℚ) : ℝ) ≤ stT262 192 := by
  have hc : ((-324111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29238377421/625000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-324111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c193 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-109971/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3307713/5000000) (δ := 6611/500000000) (ψ := -414889/500000) 262 220
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t193 : ((-39581692093/625000000000 : ℚ) : ℝ) ≤ stT262 193 := by
  have hc : ((-439909/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39581692093/625000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-439909/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c194 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((5501/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1615193/5000000) (δ := 6611/500000000) (ψ := -414889/500000) 262 220
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t194 : ((3948769/200000000 : ℚ) : ℝ) ≤ stT262 194 := by
  have hc : ((11/40 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3948769/200000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((11/40 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c195 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((499247/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 137231/10000000) (δ := 6611/500000000) (ψ := -414889/500000) 262 220
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t195 : ((89374965827/1250000000000 : ℚ) : ℝ) ≤ stT262 195 := by
  have hc : ((249611/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89374965827/1250000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((249611/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c196 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((43711/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1743811/5000000) (δ := 13181/1000000000) (ψ := -414889/500000) 262 220
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t196 : ((12485273229/1000000000000 : ℚ) : ℝ) ≤ stT262 196 := by
  have hc : ((87397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12485273229/1000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((87397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c197 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-915841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3410491/5000000) (δ := 6611/500000000) (ψ := -414889/500000) 262 220
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t197 : ((-652545776661/10000000000000 : ℚ) : ℝ) ≤ stT262 197 := by
  have hc : ((-915891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-652545776661/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-915891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c198 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-61107/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5570519/10000000) (δ := 1661/125000000) (ψ := -414889/500000) 262 221
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t198 : ((-542880813/12500000000 : ℚ) : ℝ) ≤ stT262 198 := by
  have hc : ((-7639/12500 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-542880813/12500000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-7639/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c199 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((153771/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56769/250000) (δ := 1661/125000000) (ψ := -414889/500000) 262 221
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t199 : ((217992958477/5000000000000 : ℚ) : ℝ) ≤ stT262 199 := by
  have hc : ((307517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217992958477/5000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((307517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c200 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((459557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1012427/10000000) (δ := 2623/200000000) (ψ := -414889/500000) 262 221
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t200 : ((40617229299/625000000000 : ℚ) : ℝ) ≤ stT262 200 := by
  have hc : ((114883/125000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40617229299/625000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((114883/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c201 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-7023/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 855861/2000000) (δ := 2623/200000000) (ψ := -414889/500000) 262 221
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t201 : ((-4955408323/500000000000 : ℚ) : ℝ) ≤ stT262 201 := by
  have hc : ((-14051/100000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4955408323/500000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-14051/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c202 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-123951/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3764937/5000000) (δ := 1661/125000000) (ψ := -414889/500000) 262 221
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t202 : ((-174432146371/2500000000000 : ℚ) : ℝ) ≤ stT262 202 := by
  have hc : ((-495829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174432146371/2500000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-495829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c203 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-395493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4943503/10000000) (δ := 2639/200000000) (ψ := -414889/500000) 262 222
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t203 : ((-277616996609/10000000000000 : ℚ) : ℝ) ≤ stT262 203 := by
  have hc : ((-395543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277616996609/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-395543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c204 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((771289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1724833/10000000) (δ := 2639/200000000) (ψ := -414889/500000) 262 222
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t204 : ((26998763673/500000000000 : ℚ) : ℝ) ≤ stT262 204 := by
  have hc : ((771239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26998763673/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((771239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c205 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((415123/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1478117/10000000) (δ := 2639/200000000) (ψ := -414889/500000) 262 222
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t205 : ((14495844807/250000000000 : ℚ) : ℝ) ≤ stT262 205 := by
  have hc : ((207549/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14495844807/250000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((207549/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c206 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-145559/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2332739/5000000) (δ := 2639/200000000) (ψ := -414889/500000) 262 222
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t206 : ((-3169791333/156250000000 : ℚ) : ℝ) ≤ stT262 206 := by
  have hc : ((-9099/31250 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3169791333/156250000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-9099/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c207 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-499989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7837381/10000000) (δ := 2639/200000000) (ψ := -414889/500000) 262 222
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t207 : ((-173767115343/2500000000000 : ℚ) : ℝ) ≤ stT262 207 := by
  have hc : ((-250007/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173767115343/2500000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-250007/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c208 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-309607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4713941/10000000) (δ := 13103/1000000000) (ψ := -414889/500000) 262 223
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t208 : ((-1677411969/78125000000 : ℚ) : ℝ) ≤ stT262 208 := by
  have hc : ((-309657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1677411969/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-309657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c209 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((808633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -157243/1000000) (δ := 13103/1000000000) (ψ := -414889/500000) 262 223
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t209 : ((279654090631/5000000000000 : ℚ) : ℝ) ≤ stT262 209 := by
  have hc : ((808583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((279654090631/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((808583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c210 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((812929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1554081/10000000) (δ := 133/10000000) (ψ := -414889/500000) 262 223
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t210 : ((112187869427/2000000000000 : ℚ) : ℝ) ≤ stT262 210 := by
  have hc : ((812879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112187869427/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((812879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c211 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-72803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1166431/2500000) (δ := 133/10000000) (ψ := -414889/500000) 262 223
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t211 : ((-100256603699/5000000000000 : ℚ) : ℝ) ≤ stT262 211 := by
  have hc : ((-145631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100256603699/5000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-145631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c212 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-249833/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 776263/1000000) (δ := 13103/1000000000) (ψ := -414889/500000) 262 223
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t212 : ((-343189277873/5000000000000 : ℚ) : ℝ) ≤ stT262 212 := by
  have hc : ((-499691/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-343189277873/5000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-499691/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c213 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-182853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4862969/10000000) (δ := 13193/1000000000) (ψ := -414889/500000) 262 224
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t213 : ((-62652996971/2500000000000 : ℚ) : ℝ) ≤ stT262 213 := by
  have hc : ((-91439/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62652996971/2500000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-91439/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c214 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((753119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -897507/5000000) (δ := 1321/100000000) (ψ := -414889/500000) 262 224
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t214 : ((102957334473/2000000000000 : ℚ) : ℝ) ≤ stT262 214 := by
  have hc : ((753069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102957334473/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((753069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c215 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((875929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 314649/2500000) (δ := 1321/100000000) (ψ := -414889/500000) 262 224
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t215 : ((298672111363/5000000000000 : ℚ) : ℝ) ≤ stT262 215 := by
  have hc : ((875879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298672111363/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((875879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c216 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-73941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2149029/5000000) (δ := 1321/100000000) (ψ := -414889/500000) 262 224
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t216 : ((-12581875481/1250000000000 : ℚ) : ℝ) ≤ stT262 216 := by
  have hc : ((-36983/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12581875481/1250000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-36983/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c217 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-488783/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7323437/10000000) (δ := 13193/1000000000) (ψ := -414889/500000) 262 224
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t217 : ((-8295621669/125000000000 : ℚ) : ℝ) ≤ stT262 217 := by
  have hc : ((-61101/62500 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8295621669/125000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-61101/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c218 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-546699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5373033/10000000) (δ := 6643/500000000) (ψ := -414889/500000) 262 225
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t218 : ((-185152721607/5000000000000 : ℚ) : ℝ) ≤ stT262 218 := by
  have hc : ((-546749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185152721607/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-546749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c219 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((581587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1187647/5000000) (δ := 13117/1000000000) (ψ := -414889/500000) 262 225
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t219 : ((392966067769/10000000000000 : ℚ) : ℝ) ≤ stT262 219 := by
  have hc : ((581537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((392966067769/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((581537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c220 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((1941/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 121751/2000000) (δ := 13117/1000000000) (ψ := -414889/500000) 262 225
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t220 : ((13085528391/200000000000 : ℚ) : ℝ) ≤ stT262 220 := by
  have hc : ((19409/20000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13085528391/200000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((19409/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c221 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((2166/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3579311/10000000) (δ := 13117/1000000000) (ψ := -414889/500000) 262 225
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t221 : ((1456482027/156250000000 : ℚ) : ℝ) ≤ stT262 221 := by
  have hc : ((69287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1456482027/156250000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((69287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c222 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-432149/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3268187/5000000) (δ := 13117/1000000000) (ψ := -414889/500000) 262 225
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t222 : ((-145028302659/2500000000000 : ℚ) : ℝ) ≤ stT262 222 := by
  have hc : ((-216087/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145028302659/2500000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-216087/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c223 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-795787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6227757/10000000) (δ := 1653/125000000) (ψ := -414889/500000) 262 226
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t223 : ((-10658644941/200000000000 : ℚ) : ℝ) ≤ stT262 223 := by
  have hc : ((-795837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10658644941/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-795837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c224 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((124651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3297091/10000000) (δ := 13179/1000000000) (ψ := -414889/500000) 262 226
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t224 : ((41634617889/2500000000000 : ℚ) : ℝ) ≤ stT262 224 := by
  have hc : ((62313/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41634617889/2500000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((62313/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c225 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((988503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -379459/10000000) (δ := 13179/1000000000) (ψ := -414889/500000) 262 226
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t225 : ((329484003849/5000000000000 : ℚ) : ℝ) ≤ stT262 225 := by
  have hc : ((988453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((329484003849/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((988453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c226 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((531803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2525171/10000000) (δ := 26379/1000000000) (ψ := -414889/500000) 262 226
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t226 : ((35371677807/1000000000000 : ℚ) : ℝ) ≤ stT262 226 := by
  have hc : ((531753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35371677807/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((531753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c227 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-561349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5417029/10000000) (δ := 13179/1000000000) (ψ := -414889/500000) 262 226
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t227 : ((-93153497469/2500000000000 : ℚ) : ℝ) ≤ stT262 227 := by
  have hc : ((-561399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93153497469/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-561399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c228 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-2461/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -926477/1250000) (δ := 13131/1000000000) (ψ := -414889/500000) 262 227
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t228 : ((-13039374963/200000000000 : ℚ) : ℝ) ≤ stT262 228 := by
  have hc : ((-19689/20000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13039374963/200000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-19689/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c229 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-153/625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2272637/5000000) (δ := 13131/1000000000) (ψ := -414889/500000) 262 227
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t229 : ((-3236030643/200000000000 : ℚ) : ℝ) ≤ stT262 229 := by
  have hc : ((-4897/20000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3236030643/200000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-4897/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c230 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((77977/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1691243/10000000) (δ := 1659/125000000) (ψ := -414889/500000) 262 227
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t230 : ((642664717/12500000000 : ℚ) : ℝ) ≤ stT262 230 := by
  have hc : ((19493/25000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((642664717/12500000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((19493/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c231 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((44799/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1150409/10000000) (δ := 1659/125000000) (ψ := -414889/500000) 262 227
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t231 : ((58947803943/1000000000000 : ℚ) : ℝ) ≤ stT262 231 := by
  have hc : ((89593/100000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58947803943/1000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((89593/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c232 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-21101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3979747/10000000) (δ := 1659/125000000) (ψ := -414889/500000) 262 227
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t232 : ((-13886329483/10000000000000 : ℚ) : ℝ) ≤ stT262 232 := by
  have hc : ((-21151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13886329483/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-21151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c233 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-911941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 849621/1250000) (δ := 13131/1000000000) (ψ := -414889/500000) 262 227
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t233 : ((-298732683951/5000000000000 : ℚ) : ℝ) ≤ stT262 233 := by
  have hc : ((-911991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-298732683951/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-911991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c234 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-382659/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6105827/10000000) (δ := 2633/200000000) (ψ := -414889/500000) 262 228
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t234 : ((-62542141791/1250000000000 : ℚ) : ℝ) ≤ stT262 234 := by
  have hc : ((-95671/125000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62542141791/1250000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-95671/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c235 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((243273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -662529/2000000) (δ := 2633/200000000) (ψ := -414889/500000) 262 228
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t235 : ((19832646643/1250000000000 : ℚ) : ℝ) ≤ stT262 235 := by
  have hc : ((243223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19832646643/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((243223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c236 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((977501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -265659/5000000) (δ := 6619/500000000) (ψ := -414889/500000) 262 228
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t236 : ((9941654121/156250000000 : ℚ) : ℝ) ≤ stT262 236 := by
  have hc : ((977451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9941654121/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((977451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c237 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((125059/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1119109/5000000) (δ := 2633/200000000) (ψ := -414889/500000) 262 228
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t237 : ((81227953881/2000000000000 : ℚ) : ℝ) ≤ stT262 237 := by
  have hc : ((125049/200000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81227953881/2000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((125049/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c238 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-207363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39032/78125) (δ := 6619/500000000) (ψ := -414889/500000) 262 228
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t238 : ((-8401858197/312500000000 : ℚ) : ℝ) ≤ stT262 238 := by
  have hc : ((-51847/125000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8401858197/312500000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-51847/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c239 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-199801/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1548489/2000000) (δ := 2633/200000000) (ψ := -414889/500000) 262 228
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t239 : ((-129247145917/2000000000000 : ℚ) : ℝ) ≤ stT262 239 := by
  have hc : ((-199811/200000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129247145917/2000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-199811/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c240 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-498143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5230631/10000000) (δ := 6573/500000000) (ψ := -414889/500000) 262 229
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t240 : ((-160791292557/5000000000000 : ℚ) : ℝ) ≤ stT262 240 := by
  have hc : ((-498193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160791292557/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-498193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c241 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((537897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2507141/10000000) (δ := 6573/500000000) (ψ := -414889/500000) 262 229
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t241 : ((86614343033/2500000000000 : ℚ) : ℝ) ≤ stT262 241 := by
  have hc : ((537847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86614343033/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((537847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c242 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((996637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 205083/10000000) (δ := 6573/500000000) (ψ := -414889/500000) 262 229
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t242 : ((80078755211/1250000000000 : ℚ) : ℝ) ≤ stT262 242 := by
  have hc : ((996587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80078755211/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((996587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c243 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((397099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1453053/5000000) (δ := 13257/1000000000) (ψ := -414889/500000) 262 229
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t243 : ((509413867/20000000000 : ℚ) : ℝ) ≤ stT262 243 := by
  have hc : ((397049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((509413867/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((397049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c244 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-4953/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 279803/500000) (δ := 13257/1000000000) (ψ := -414889/500000) 262 229
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t244 : ((-3171092379/80000000000 : ℚ) : ℝ) ≤ stT262 244 := by
  have hc : ((-24767/40000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3171092379/80000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-24767/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c245 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-492927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3716493/5000000) (δ := 527/20000000) (ψ := -414889/500000) 262 230
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t245 : ((-39366961863/625000000000 : ℚ) : ℝ) ≤ stT262 245 := by
  have hc : ((-61619/62500 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39366961863/625000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-61619/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c246 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-328939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4764941/10000000) (δ := 13253/1000000000) (ψ := -414889/500000) 262 230
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t246 : ((-209755819653/10000000000000 : ℚ) : ℝ) ≤ stT262 246 := by
  have hc : ((-328989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209755819653/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-328989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c247 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((133031/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2107737/10000000) (δ := 13253/1000000000) (ψ := -414889/500000) 262 230
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t247 : ((21159783491/500000000000 : ℚ) : ℝ) ≤ stT262 247 := by
  have hc : ((133021/200000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21159783491/500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((133021/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c248 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((122109/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21549/400000) (δ := 13253/1000000000) (ψ := -414889/500000) 262 230
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t248 : ((62028197/1000000000 : ℚ) : ℝ) ≤ stT262 248 := by
  have hc : ((488411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62028197/1000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((488411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c249 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((74117/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 317451/1000000) (δ := 263/20000000) (ψ := -414889/500000) 262 230
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t249 : ((23480900079/1250000000000 : ℚ) : ℝ) ≤ stT262 249 := by
  have hc : ((148209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23480900079/1250000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((148209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_c250 :
    |Real.cos (((262 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((-340501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 724977/1250000) (δ := 13253/1000000000) (ψ := -414889/500000) 262 230
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st262_t250 : ((-13460481991/312500000000 : ℚ) : ℝ) ≤ stT262 250 := by
  have hc : ((-170263/250000 : ℚ) : ℝ)
      ≤ Real.cos (((262 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st262_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13460481991/312500000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-170263/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st262_p1 : ((67499/100000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT262 (i+1) := by
  rw [Finset.sum_range_one]
  exact st262_t1

theorem st262_p2 : ((6823573015503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT262 (i+1))
      = (∑ i ∈ Finset.range 1, stT262 (i+1)) + stT262 2 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 1
    simpa using h
  have hprev := st262_p1
  have hstep := st262_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p3 : ((9524786755231/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT262 (i+1))
      = (∑ i ∈ Finset.range 2, stT262 (i+1)) + stT262 3 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 2
    simpa using h
  have hprev := st262_p2
  have hstep := st262_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p4 : ((11840859255231/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT262 (i+1))
      = (∑ i ∈ Finset.range 3, stT262 (i+1)) + stT262 4 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 3
    simpa using h
  have hprev := st262_p3
  have hstep := st262_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p5 : ((23867889018377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT262 (i+1))
      = (∑ i ∈ Finset.range 4, stT262 (i+1)) + stT262 5 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 4
    simpa using h
  have hprev := st262_p4
  have hstep := st262_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p6 : ((26181758166337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT262 (i+1))
      = (∑ i ∈ Finset.range 5, stT262 (i+1)) + stT262 6 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 5
    simpa using h
  have hprev := st262_p5
  have hstep := st262_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p7 : ((25618870755067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT262 (i+1))
      = (∑ i ∈ Finset.range 6, stT262 (i+1)) + stT262 7 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 6
    simpa using h
  have hprev := st262_p6
  have hstep := st262_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p8 : ((27547779778141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT262 (i+1))
      = (∑ i ∈ Finset.range 7, stT262 (i+1)) + stT262 8 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 7
    simpa using h
  have hprev := st262_p7
  have hstep := st262_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p9 : ((6903867442843/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT262 (i+1))
      = (∑ i ∈ Finset.range 8, stT262 (i+1)) + stT262 9 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 8
    simpa using h
  have hprev := st262_p8
  have hstep := st262_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p10 : ((14763941042669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT262 (i+1))
      = (∑ i ∈ Finset.range 9, stT262 (i+1)) + stT262 10 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 9
    simpa using h
  have hprev := st262_p9
  have hstep := st262_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p11 : ((7928400957881/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT262 (i+1))
      = (∑ i ∈ Finset.range 10, stT262 (i+1)) + stT262 11 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 10
    simpa using h
  have hprev := st262_p10
  have hstep := st262_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p12 : ((7924644571841/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT262 (i+1))
      = (∑ i ∈ Finset.range 11, stT262 (i+1)) + stT262 12 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 11
    simpa using h
  have hprev := st262_p11
  have hstep := st262_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p13 : ((2129322379679/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT262 (i+1))
      = (∑ i ∈ Finset.range 12, stT262 (i+1)) + stT262 13 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 12
    simpa using h
  have hprev := st262_p12
  have hstep := st262_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p14 : ((1762581827299/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT262 (i+1))
      = (∑ i ∈ Finset.range 13, stT262 (i+1)) + stT262 14 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 13
    simpa using h
  have hprev := st262_p13
  have hstep := st262_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p15 : ((9421636045387/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT262 (i+1))
      = (∑ i ∈ Finset.range 14, stT262 (i+1)) + stT262 15 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 14
    simpa using h
  have hprev := st262_p14
  have hstep := st262_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p16 : ((18804879575417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT262 (i+1))
      = (∑ i ∈ Finset.range 15, stT262 (i+1)) + stT262 16 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 15
    simpa using h
  have hprev := st262_p15
  have hstep := st262_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p17 : ((18629579622171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT262 (i+1))
      = (∑ i ∈ Finset.range 16, stT262 (i+1)) + stT262 17 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 16
    simpa using h
  have hprev := st262_p16
  have hstep := st262_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p18 : ((4494085620709/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT262 (i+1))
      = (∑ i ∈ Finset.range 17, stT262 (i+1)) + stT262 18 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 17
    simpa using h
  have hprev := st262_p17
  have hstep := st262_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p19 : ((37897512973439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT262 (i+1))
      = (∑ i ∈ Finset.range 18, stT262 (i+1)) + stT262 19 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 18
    simpa using h
  have hprev := st262_p18
  have hstep := st262_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p20 : ((20012253430623/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT262 (i+1))
      = (∑ i ∈ Finset.range 19, stT262 (i+1)) + stT262 20 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 19
    simpa using h
  have hprev := st262_p19
  have hstep := st262_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p21 : ((209535282733/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT262 (i+1))
      = (∑ i ∈ Finset.range 20, stT262 (i+1)) + stT262 21 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 20
    simpa using h
  have hprev := st262_p20
  have hstep := st262_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p22 : ((44014377037547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT262 (i+1))
      = (∑ i ∈ Finset.range 21, stT262 (i+1)) + stT262 22 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 21
    simpa using h
  have hprev := st262_p21
  have hstep := st262_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p23 : ((45514114774403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT262 (i+1))
      = (∑ i ∈ Finset.range 22, stT262 (i+1)) + stT262 23 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 22
    simpa using h
  have hprev := st262_p22
  have hstep := st262_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p24 : ((44339700478397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT262 (i+1))
      = (∑ i ∈ Finset.range 23, stT262 (i+1)) + stT262 24 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 23
    simpa using h
  have hprev := st262_p23
  have hstep := st262_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p25 : ((43117123867109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT262 (i+1))
      = (∑ i ∈ Finset.range 24, stT262 (i+1)) + stT262 25 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 24
    simpa using h
  have hprev := st262_p24
  have hstep := st262_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p26 : ((4507440372949/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT262 (i+1))
      = (∑ i ∈ Finset.range 25, stT262 (i+1)) + stT262 26 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 25
    simpa using h
  have hprev := st262_p25
  have hstep := st262_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p27 : ((4330251565879/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT262 (i+1))
      = (∑ i ∈ Finset.range 26, stT262 (i+1)) + stT262 27 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 26
    simpa using h
  have hprev := st262_p26
  have hstep := st262_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p28 : ((22478349766627/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT262 (i+1))
      = (∑ i ∈ Finset.range 27, stT262 (i+1)) + stT262 28 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 27
    simpa using h
  have hprev := st262_p27
  have hstep := st262_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p29 : ((10792200020413/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT262 (i+1))
      = (∑ i ∈ Finset.range 28, stT262 (i+1)) + stT262 29 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 28
    simpa using h
  have hprev := st262_p28
  have hstep := st262_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p30 : ((11232218207341/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT262 (i+1))
      = (∑ i ∈ Finset.range 29, stT262 (i+1)) + stT262 30 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 29
    simpa using h
  have hprev := st262_p29
  have hstep := st262_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p31 : ((22059175688149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT262 (i+1))
      = (∑ i ∈ Finset.range 30, stT262 (i+1)) + stT262 31 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 30
    simpa using h
  have hprev := st262_p30
  have hstep := st262_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p32 : ((43064721585657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT262 (i+1))
      = (∑ i ∈ Finset.range 31, stT262 (i+1)) + stT262 32 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 31
    simpa using h
  have hprev := st262_p31
  have hstep := st262_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p33 : ((44646723147473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT262 (i+1))
      = (∑ i ∈ Finset.range 32, stT262 (i+1)) + stT262 33 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 32
    simpa using h
  have hprev := st262_p32
  have hstep := st262_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p34 : ((45412292451473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT262 (i+1))
      = (∑ i ∈ Finset.range 33, stT262 (i+1)) + stT262 34 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 33
    simpa using h
  have hprev := st262_p33
  have hstep := st262_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p35 : ((8828742433271/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT262 (i+1))
      = (∑ i ∈ Finset.range 34, stT262 (i+1)) + stT262 35 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 34
    simpa using h
  have hprev := st262_p34
  have hstep := st262_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p36 : ((8518622371247/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT262 (i+1))
      = (∑ i ∈ Finset.range 35, stT262 (i+1)) + stT262 36 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 35
    simpa using h
  have hprev := st262_p35
  have hstep := st262_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p37 : ((1684293893401/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT262 (i+1))
      = (∑ i ∈ Finset.range 36, stT262 (i+1)) + stT262 37 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 36
    simpa using h
  have hprev := st262_p36
  have hstep := st262_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p38 : ((8548985220689/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT262 (i+1))
      = (∑ i ∈ Finset.range 37, stT262 (i+1)) + stT262 38 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 37
    simpa using h
  have hprev := st262_p37
  have hstep := st262_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p39 : ((22012492665501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT262 (i+1))
      = (∑ i ∈ Finset.range 38, stT262 (i+1)) + stT262 39 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 38
    simpa using h
  have hprev := st262_p38
  have hstep := st262_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p40 : ((5692255534017/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT262 (i+1))
      = (∑ i ∈ Finset.range 39, stT262 (i+1)) + stT262 40 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 39
    simpa using h
  have hprev := st262_p39
  have hstep := st262_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p41 : ((11772648002907/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT262 (i+1))
      = (∑ i ∈ Finset.range 40, stT262 (i+1)) + stT262 41 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 40
    simpa using h
  have hprev := st262_p40
  have hstep := st262_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p42 : ((972577881449/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT262 (i+1))
      = (∑ i ∈ Finset.range 41, stT262 (i+1)) + stT262 42 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 41
    simpa using h
  have hprev := st262_p41
  have hstep := st262_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p43 : ((5012464206003/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT262 (i+1))
      = (∑ i ∈ Finset.range 42, stT262 (i+1)) + stT262 43 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 42
    simpa using h
  have hprev := st262_p42
  have hstep := st262_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p44 : ((25739103622427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT262 (i+1))
      = (∑ i ∈ Finset.range 43, stT262 (i+1)) + stT262 44 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 43
    simpa using h
  have hprev := st262_p43
  have hstep := st262_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p45 : ((26230358488211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT262 (i+1))
      = (∑ i ∈ Finset.range 44, stT262 (i+1)) + stT262 45 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 44
    simpa using h
  have hprev := st262_p44
  have hstep := st262_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p46 : ((26373138275333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT262 (i+1))
      = (∑ i ∈ Finset.range 45, stT262 (i+1)) + stT262 46 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 45
    simpa using h
  have hprev := st262_p45
  have hstep := st262_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p47 : ((26053524721933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT262 (i+1))
      = (∑ i ∈ Finset.range 46, stT262 (i+1)) + stT262 47 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 46
    simpa using h
  have hprev := st262_p46
  have hstep := st262_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p48 : ((25375560911101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT262 (i+1))
      = (∑ i ∈ Finset.range 47, stT262 (i+1)) + stT262 48 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 47
    simpa using h
  have hprev := st262_p47
  have hstep := st262_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p49 : ((24759569950419/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT262 (i+1))
      = (∑ i ∈ Finset.range 48, stT262 (i+1)) + stT262 49 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 48
    simpa using h
  have hprev := st262_p48
  have hstep := st262_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p50 : ((6181081050501/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT262 (i+1))
      = (∑ i ∈ Finset.range 49, stT262 (i+1)) + stT262 50 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 49
    simpa using h
  have hprev := st262_p49
  have hstep := st262_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p51 : ((3166236073833/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT262 (i+1))
      = (∑ i ∈ Finset.range 50, stT262 (i+1)) + stT262 51 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 50
    simpa using h
  have hprev := st262_p50
  have hstep := st262_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p52 : ((6468341059041/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT262 (i+1))
      = (∑ i ∈ Finset.range 51, stT262 (i+1)) + stT262 52 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 51
    simpa using h
  have hprev := st262_p51
  have hstep := st262_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p53 : ((12805569364973/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT262 (i+1))
      = (∑ i ∈ Finset.range 52, stT262 (i+1)) + stT262 53 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 52
    simpa using h
  have hprev := st262_p52
  have hstep := st262_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p54 : ((12472591083309/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT262 (i+1))
      = (∑ i ∈ Finset.range 53, stT262 (i+1)) + stT262 54 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 53
    simpa using h
  have hprev := st262_p53
  have hstep := st262_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p55 : ((50040571936639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT262 (i+1))
      = (∑ i ∈ Finset.range 54, stT262 (i+1)) + stT262 55 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 54
    simpa using h
  have hprev := st262_p54
  have hstep := st262_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p56 : ((51369697964501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT262 (i+1))
      = (∑ i ∈ Finset.range 55, stT262 (i+1)) + stT262 56 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 55
    simpa using h
  have hprev := st262_p55
  have hstep := st262_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p57 : ((2045387866823/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT262 (i+1))
      = (∑ i ∈ Finset.range 56, stT262 (i+1)) + stT262 57 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 56
    simpa using h
  have hprev := st262_p56
  have hstep := st262_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p58 : ((2494707546873/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT262 (i+1))
      = (∑ i ∈ Finset.range 57, stT262 (i+1)) + stT262 58 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 57
    simpa using h
  have hprev := st262_p57
  have hstep := st262_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p59 : ((6324264270261/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT262 (i+1))
      = (∑ i ∈ Finset.range 58, stT262 (i+1)) + stT262 59 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 58
    simpa using h
  have hprev := st262_p58
  have hstep := st262_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p60 : ((25709974411477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT262 (i+1))
      = (∑ i ∈ Finset.range 59, stT262 (i+1)) + stT262 60 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 59
    simpa using h
  have hprev := st262_p59
  have hstep := st262_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p61 : ((6275188268751/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT262 (i+1))
      = (∑ i ∈ Finset.range 60, stT262 (i+1)) + stT262 61 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 60
    simpa using h
  have hprev := st262_p60
  have hstep := st262_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p62 : ((12594568762299/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT262 (i+1))
      = (∑ i ∈ Finset.range 61, stT262 (i+1)) + stT262 62 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 61
    simpa using h
  have hprev := st262_p61
  have hstep := st262_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p63 : ((51373526864313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT262 (i+1))
      = (∑ i ∈ Finset.range 62, stT262 (i+1)) + stT262 63 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 62
    simpa using h
  have hprev := st262_p62
  have hstep := st262_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p64 : ((3136793416653/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT262 (i+1))
      = (∑ i ∈ Finset.range 63, stT262 (i+1)) + stT262 64 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 63
    simpa using h
  have hprev := st262_p63
  have hstep := st262_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p65 : ((50585629273041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT262 (i+1))
      = (∑ i ∈ Finset.range 64, stT262 (i+1)) + stT262 65 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 64
    simpa using h
  have hprev := st262_p64
  have hstep := st262_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p66 : ((51210689864069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT262 (i+1))
      = (∑ i ∈ Finset.range 65, stT262 (i+1)) + stT262 66 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 65
    simpa using h
  have hprev := st262_p65
  have hstep := st262_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p67 : ((6252985351023/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT262 (i+1))
      = (∑ i ∈ Finset.range 66, stT262 (i+1)) + stT262 67 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 66
    simpa using h
  have hprev := st262_p66
  have hstep := st262_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p68 : ((25543966889913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT262 (i+1))
      = (∑ i ∈ Finset.range 67, stT262 (i+1)) + stT262 68 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 67
    simpa using h
  have hprev := st262_p67
  have hstep := st262_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p69 : ((25316589225147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT262 (i+1))
      = (∑ i ∈ Finset.range 68, stT262 (i+1)) + stT262 69 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 68
    simpa using h
  have hprev := st262_p68
  have hstep := st262_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p70 : ((50347921511467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT262 (i+1))
      = (∑ i ∈ Finset.range 69, stT262 (i+1)) + stT262 70 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 69
    simpa using h
  have hprev := st262_p69
  have hstep := st262_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p71 : ((5121209152477/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT262 (i+1))
      = (∑ i ∈ Finset.range 70, stT262 (i+1)) + stT262 71 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 70
    simpa using h
  have hprev := st262_p70
  have hstep := st262_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p72 : ((25032583590953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT262 (i+1))
      = (∑ i ∈ Finset.range 71, stT262 (i+1)) + stT262 72 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 71
    simpa using h
  have hprev := st262_p71
  have hstep := st262_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p73 : ((25600989011459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT262 (i+1))
      = (∑ i ∈ Finset.range 72, stT262 (i+1)) + stT262 73 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 72
    simpa using h
  have hprev := st262_p72
  have hstep := st262_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p74 : ((50285756663167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT262 (i+1))
      = (∑ i ∈ Finset.range 73, stT262 (i+1)) + stT262 74 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 73
    simpa using h
  have hprev := st262_p73
  have hstep := st262_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p75 : ((50871905477167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT262 (i+1))
      = (∑ i ∈ Finset.range 74, stT262 (i+1)) + stT262 75 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 74
    simpa using h
  have hprev := st262_p74
  have hstep := st262_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p76 : ((50639656392037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT262 (i+1))
      = (∑ i ∈ Finset.range 75, stT262 (i+1)) + stT262 76 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 75
    simpa using h
  have hprev := st262_p75
  have hstep := st262_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p77 : ((50549131789427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT262 (i+1))
      = (∑ i ∈ Finset.range 76, stT262 (i+1)) + stT262 77 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 76
    simpa using h
  have hprev := st262_p76
  have hstep := st262_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p78 : ((50903711125639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT262 (i+1))
      = (∑ i ∈ Finset.range 77, stT262 (i+1)) + stT262 78 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 77
    simpa using h
  have hprev := st262_p77
  have hstep := st262_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p79 : ((50349909059399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT262 (i+1))
      = (∑ i ∈ Finset.range 78, stT262 (i+1)) + stT262 79 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 78
    simpa using h
  have hprev := st262_p78
  have hstep := st262_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p80 : ((51042948647241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT262 (i+1))
      = (∑ i ∈ Finset.range 79, stT262 (i+1)) + stT262 80 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 79
    simpa using h
  have hprev := st262_p79
  have hstep := st262_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p81 : ((50260091354289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT262 (i+1))
      = (∑ i ∈ Finset.range 80, stT262 (i+1)) + stT262 81 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 80
    simpa using h
  have hprev := st262_p80
  have hstep := st262_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p82 : ((6386657848503/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT262 (i+1))
      = (∑ i ∈ Finset.range 81, stT262 (i+1)) + stT262 82 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 81
    simpa using h
  have hprev := st262_p81
  have hstep := st262_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p83 : ((50240858480013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT262 (i+1))
      = (∑ i ∈ Finset.range 82, stT262 (i+1)) + stT262 83 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 82
    simpa using h
  have hprev := st262_p82
  have hstep := st262_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p84 : ((1596419281611/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT262 (i+1))
      = (∑ i ∈ Finset.range 83, stT262 (i+1)) + stT262 84 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 83
    simpa using h
  have hprev := st262_p83
  have hstep := st262_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p85 : ((5027455862973/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT262 (i+1))
      = (∑ i ∈ Finset.range 84, stT262 (i+1)) + stT262 85 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 84
    simpa using h
  have hprev := st262_p84
  have hstep := st262_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p86 : ((51022907862787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT262 (i+1))
      = (∑ i ∈ Finset.range 85, stT262 (i+1)) + stT262 86 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 85
    simpa using h
  have hprev := st262_p85
  have hstep := st262_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p87 : ((25185117207719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT262 (i+1))
      = (∑ i ∈ Finset.range 86, stT262 (i+1)) + stT262 87 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 86
    simpa using h
  have hprev := st262_p86
  have hstep := st262_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p88 : ((50887950498421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT262 (i+1))
      = (∑ i ∈ Finset.range 87, stT262 (i+1)) + stT262 88 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 87
    simpa using h
  have hprev := st262_p87
  have hstep := st262_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p89 : ((50548373779133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT262 (i+1))
      = (∑ i ∈ Finset.range 88, stT262 (i+1)) + stT262 89 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 88
    simpa using h
  have hprev := st262_p88
  have hstep := st262_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p90 : ((50665991472677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT262 (i+1))
      = (∑ i ∈ Finset.range 89, stT262 (i+1)) + stT262 90 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 89
    simpa using h
  have hprev := st262_p89
  have hstep := st262_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p91 : ((50806681668317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT262 (i+1))
      = (∑ i ∈ Finset.range 90, stT262 (i+1)) + stT262 91 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 90
    simpa using h
  have hprev := st262_p90
  have hstep := st262_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p92 : ((50388328400607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT262 (i+1))
      = (∑ i ∈ Finset.range 91, stT262 (i+1)) + stT262 92 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 91
    simpa using h
  have hprev := st262_p91
  have hstep := st262_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p93 : ((51073572582133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT262 (i+1))
      = (∑ i ∈ Finset.range 92, stT262 (i+1)) + stT262 93 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 92
    simpa using h
  have hprev := st262_p92
  have hstep := st262_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p94 : ((10034608844493/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT262 (i+1))
      = (∑ i ∈ Finset.range 93, stT262 (i+1)) + stT262 94 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 93
    simpa using h
  have hprev := st262_p93
  have hstep := st262_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p95 : ((51188888637759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT262 (i+1))
      = (∑ i ∈ Finset.range 94, stT262 (i+1)) + stT262 95 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 94
    simpa using h
  have hprev := st262_p94
  have hstep := st262_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p96 : ((25100973555069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT262 (i+1))
      = (∑ i ∈ Finset.range 95, stT262 (i+1)) + stT262 96 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 95
    simpa using h
  have hprev := st262_p95
  have hstep := st262_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p97 : ((5098861891471/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT262 (i+1))
      = (∑ i ∈ Finset.range 96, stT262 (i+1)) + stT262 97 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 96
    simpa using h
  have hprev := st262_p96
  have hstep := st262_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p98 : ((25282787459767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT262 (i+1))
      = (∑ i ∈ Finset.range 97, stT262 (i+1)) + stT262 98 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 97
    simpa using h
  have hprev := st262_p97
  have hstep := st262_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p99 : ((25257845431721/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT262 (i+1))
      = (∑ i ∈ Finset.range 98, stT262 (i+1)) + stT262 99 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 98
    simpa using h
  have hprev := st262_p98
  have hstep := st262_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p100 : ((25522573166993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT262 (i+1))
      = (∑ i ∈ Finset.range 99, stT262 (i+1)) + stT262 100 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 99
    simpa using h
  have hprev := st262_p99
  have hstep := st262_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p101 : ((3135104561849/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT262 (i+1))
      = (∑ i ∈ Finset.range 100, stT262 (i+1)) + stT262 101 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 100
    simpa using h
  have hprev := st262_p100
  have hstep := st262_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p102 : ((25574217833569/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT262 (i+1))
      = (∑ i ∈ Finset.range 101, stT262 (i+1)) + stT262 102 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 101
    simpa using h
  have hprev := st262_p101
  have hstep := st262_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p103 : ((25187296478509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT262 (i+1))
      = (∑ i ∈ Finset.range 102, stT262 (i+1)) + stT262 103 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 102
    simpa using h
  have hprev := st262_p102
  have hstep := st262_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p104 : ((25328893211089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT262 (i+1))
      = (∑ i ∈ Finset.range 103, stT262 (i+1)) + stT262 104 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 103
    simpa using h
  have hprev := st262_p103
  have hstep := st262_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p105 : ((25492217395339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT262 (i+1))
      = (∑ i ∈ Finset.range 104, stT262 (i+1)) + stT262 105 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 104
    simpa using h
  have hprev := st262_p104
  have hstep := st262_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p106 : ((12541830982829/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT262 (i+1))
      = (∑ i ∈ Finset.range 105, stT262 (i+1)) + stT262 106 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 105
    simpa using h
  have hprev := st262_p105
  have hstep := st262_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p107 : ((2556407368697/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT262 (i+1))
      = (∑ i ∈ Finset.range 106, stT262 (i+1)) + stT262 107 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 106
    simpa using h
  have hprev := st262_p106
  have hstep := st262_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p108 : ((50467815134453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT262 (i+1))
      = (∑ i ∈ Finset.range 107, stT262 (i+1)) + stT262 108 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 107
    simpa using h
  have hprev := st262_p107
  have hstep := st262_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p109 : ((50495913917989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT262 (i+1))
      = (∑ i ∈ Finset.range 108, stT262 (i+1)) + stT262 109 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 108
    simpa using h
  have hprev := st262_p108
  have hstep := st262_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p110 : ((51124196749427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT262 (i+1))
      = (∑ i ∈ Finset.range 109, stT262 (i+1)) + stT262 110 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 109
    simpa using h
  have hprev := st262_p109
  have hstep := st262_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p111 : ((50178087444923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT262 (i+1))
      = (∑ i ∈ Finset.range 110, stT262 (i+1)) + stT262 111 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 110
    simpa using h
  have hprev := st262_p110
  have hstep := st262_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p112 : ((25446995379937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT262 (i+1))
      = (∑ i ∈ Finset.range 111, stT262 (i+1)) + stT262 112 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 111
    simpa using h
  have hprev := st262_p111
  have hstep := st262_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p113 : ((50849659282749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT262 (i+1))
      = (∑ i ∈ Finset.range 112, stT262 (i+1)) + stT262 113 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 112
    simpa using h
  have hprev := st262_p112
  have hstep := st262_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p114 : ((10037373280943/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT262 (i+1))
      = (∑ i ∈ Finset.range 113, stT262 (i+1)) + stT262 114 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 113
    simpa using h
  have hprev := st262_p113
  have hstep := st262_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p115 : ((51117124935083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT262 (i+1))
      = (∑ i ∈ Finset.range 114, stT262 (i+1)) + stT262 115 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 114
    simpa using h
  have hprev := st262_p114
  have hstep := st262_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p116 : ((10114177783461/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT262 (i+1))
      = (∑ i ∈ Finset.range 115, stT262 (i+1)) + stT262 116 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 115
    simpa using h
  have hprev := st262_p115
  have hstep := st262_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p117 : ((2013193750863/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT262 (i+1))
      = (∑ i ∈ Finset.range 116, stT262 (i+1)) + stT262 117 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 116
    simpa using h
  have hprev := st262_p116
  have hstep := st262_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p118 : ((51179385361161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT262 (i+1))
      = (∑ i ∈ Finset.range 117, stT262 (i+1)) + stT262 118 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 117
    simpa using h
  have hprev := st262_p117
  have hstep := st262_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p119 : ((50390894049903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT262 (i+1))
      = (∑ i ∈ Finset.range 118, stT262 (i+1)) + stT262 119 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 118
    simpa using h
  have hprev := st262_p118
  have hstep := st262_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p120 : ((50469577966683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT262 (i+1))
      = (∑ i ∈ Finset.range 119, stT262 (i+1)) + stT262 120 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 119
    simpa using h
  have hprev := st262_p119
  have hstep := st262_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p121 : ((51170756356413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT262 (i+1))
      = (∑ i ∈ Finset.range 120, stT262 (i+1)) + stT262 121 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 120
    simpa using h
  have hprev := st262_p120
  have hstep := st262_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p122 : ((50304557805987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT262 (i+1))
      = (∑ i ∈ Finset.range 121, stT262 (i+1)) + stT262 122 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 121
    simpa using h
  have hprev := st262_p121
  have hstep := st262_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p123 : ((10109459584163/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT262 (i+1))
      = (∑ i ∈ Finset.range 122, stT262 (i+1)) + stT262 123 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 122
    simpa using h
  have hprev := st262_p122
  have hstep := st262_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p124 : ((51157737380497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT262 (i+1))
      = (∑ i ∈ Finset.range 123, stT262 (i+1)) + stT262 124 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 123
    simpa using h
  have hprev := st262_p123
  have hstep := st262_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p125 : ((10056728124673/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT262 (i+1))
      = (∑ i ∈ Finset.range 124, stT262 (i+1)) + stT262 125 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 124
    simpa using h
  have hprev := st262_p124
  have hstep := st262_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p126 : ((10109885803051/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT262 (i+1))
      = (∑ i ∈ Finset.range 125, stT262 (i+1)) + stT262 126 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 125
    simpa using h
  have hprev := st262_p125
  have hstep := st262_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p127 : ((51165473256187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT262 (i+1))
      = (∑ i ∈ Finset.range 126, stT262 (i+1)) + stT262 127 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 126
    simpa using h
  have hprev := st262_p126
  have hstep := st262_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p128 : ((50316783749299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT262 (i+1))
      = (∑ i ∈ Finset.range 127, stT262 (i+1)) + stT262 128 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 127
    simpa using h
  have hprev := st262_p127
  have hstep := st262_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p129 : ((50478538262399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT262 (i+1))
      = (∑ i ∈ Finset.range 128, stT262 (i+1)) + stT262 129 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 128
    simpa using h
  have hprev := st262_p128
  have hstep := st262_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p130 : ((51183449949333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT262 (i+1))
      = (∑ i ∈ Finset.range 129, stT262 (i+1)) + stT262 130 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 129
    simpa using h
  have hprev := st262_p129
  have hstep := st262_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p131 : ((3150955695903/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT262 (i+1))
      = (∑ i ∈ Finset.range 130, stT262 (i+1)) + stT262 131 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 130
    simpa using h
  have hprev := st262_p130
  have hstep := st262_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p132 : ((10069985506343/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT262 (i+1))
      = (∑ i ∈ Finset.range 131, stT262 (i+1)) + stT262 132 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 131
    simpa using h
  have hprev := st262_p131
  have hstep := st262_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p133 : ((6396224662563/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT262 (i+1))
      = (∑ i ∈ Finset.range 132, stT262 (i+1)) + stT262 133 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 132
    simpa using h
  have hprev := st262_p132
  have hstep := st262_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p134 : ((25299026256903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT262 (i+1))
      = (∑ i ∈ Finset.range 133, stT262 (i+1)) + stT262 134 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 133
    simpa using h
  have hprev := st262_p133
  have hstep := st262_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p135 : ((50207897623309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT262 (i+1))
      = (∑ i ∈ Finset.range 134, stT262 (i+1)) + stT262 135 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 134
    simpa using h
  have hprev := st262_p134
  have hstep := st262_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p136 : ((51060383585013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT262 (i+1))
      = (∑ i ∈ Finset.range 135, stT262 (i+1)) + stT262 136 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 135
    simpa using h
  have hprev := st262_p135
  have hstep := st262_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p137 : ((10171285223421/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT262 (i+1))
      = (∑ i ∈ Finset.range 136, stT262 (i+1)) + stT262 137 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 136
    simpa using h
  have hprev := st262_p136
  have hstep := st262_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p138 : ((25071158843073/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT262 (i+1))
      = (∑ i ∈ Finset.range 137, stT262 (i+1)) + stT262 138 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 137
    simpa using h
  have hprev := st262_p137
  have hstep := st262_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p139 : ((25402437326609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT262 (i+1))
      = (∑ i ∈ Finset.range 138, stT262 (i+1)) + stT262 139 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 138
    simpa using h
  have hprev := st262_p138
  have hstep := st262_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p140 : ((12776996227387/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT262 (i+1))
      = (∑ i ∈ Finset.range 139, stT262 (i+1)) + stT262 140 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 139
    simpa using h
  have hprev := st262_p139
  have hstep := st262_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p141 : ((12567007099953/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT262 (i+1))
      = (∑ i ∈ Finset.range 140, stT262 (i+1)) + stT262 141 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 140
    simpa using h
  have hprev := st262_p140
  have hstep := st262_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p142 : ((5044120011261/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT262 (i+1))
      = (∑ i ∈ Finset.range 141, stT262 (i+1)) + stT262 142 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 141
    simpa using h
  have hprev := st262_p141
  have hstep := st262_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p143 : ((25592273666899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT262 (i+1))
      = (∑ i ∈ Finset.range 142, stT262 (i+1)) + stT262 143 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 142
    simpa using h
  have hprev := st262_p142
  have hstep := st262_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p144 : ((1265708734721/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT262 (i+1))
      = (∑ i ∈ Finset.range 143, stT262 (i+1)) + stT262 144 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 143
    simpa using h
  have hprev := st262_p143
  have hstep := st262_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p145 : ((10032191371603/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT262 (i+1))
      = (∑ i ∈ Finset.range 144, stT262 (i+1)) + stT262 145 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 144
    simpa using h
  have hprev := st262_p144
  have hstep := st262_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p146 : ((2037326545381/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT262 (i+1))
      = (∑ i ∈ Finset.range 145, stT262 (i+1)) + stT262 146 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 145
    simpa using h
  have hprev := st262_p145
  have hstep := st262_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p147 : ((51056567291059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT262 (i+1))
      = (∑ i ∈ Finset.range 146, stT262 (i+1)) + stT262 147 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 146
    simpa using h
  have hprev := st262_p146
  have hstep := st262_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p148 : ((50235785555679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT262 (i+1))
      = (∑ i ∈ Finset.range 147, stT262 (i+1)) + stT262 148 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 147
    simpa using h
  have hprev := st262_p147
  have hstep := st262_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p149 : ((50437463843259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT262 (i+1))
      = (∑ i ∈ Finset.range 148, stT262 (i+1)) + stT262 149 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 148
    simpa using h
  have hprev := st262_p148
  have hstep := st262_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p150 : ((51179425189403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT262 (i+1))
      = (∑ i ∈ Finset.range 149, stT262 (i+1)) + stT262 150 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 149
    simpa using h
  have hprev := st262_p149
  have hstep := st262_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p151 : ((50719499315429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT262 (i+1))
      = (∑ i ∈ Finset.range 150, stT262 (i+1)) + stT262 151 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 150
    simpa using h
  have hprev := st262_p150
  have hstep := st262_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p152 : ((50131069661317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT262 (i+1))
      = (∑ i ∈ Finset.range 151, stT262 (i+1)) + stT262 152 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 151
    simpa using h
  have hprev := st262_p151
  have hstep := st262_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p153 : ((50767516222249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT262 (i+1))
      = (∑ i ∈ Finset.range 152, stT262 (i+1)) + stT262 153 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 152
    simpa using h
  have hprev := st262_p152
  have hstep := st262_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p154 : ((51173689995527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT262 (i+1))
      = (∑ i ∈ Finset.range 153, stT262 (i+1)) + stT262 154 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 153
    simpa using h
  have hprev := st262_p153
  have hstep := st262_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p155 : ((50434884223427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT262 (i+1))
      = (∑ i ∈ Finset.range 154, stT262 (i+1)) + stT262 155 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 154
    simpa using h
  have hprev := st262_p154
  have hstep := st262_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p156 : ((50206482162793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT262 (i+1))
      = (∑ i ∈ Finset.range 155, stT262 (i+1)) + stT262 156 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 155
    simpa using h
  have hprev := st262_p155
  have hstep := st262_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p157 : ((50990776438627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT262 (i+1))
      = (∑ i ∈ Finset.range 156, stT262 (i+1)) + stT262 157 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 156
    simpa using h
  have hprev := st262_p156
  have hstep := st262_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p158 : ((51064787106337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT262 (i+1))
      = (∑ i ∈ Finset.range 157, stT262 (i+1)) + stT262 158 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 157
    simpa using h
  have hprev := st262_p157
  have hstep := st262_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p159 : ((50271743829909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT262 (i+1))
      = (∑ i ∈ Finset.range 158, stT262 (i+1)) + stT262 159 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 158
    simpa using h
  have hprev := st262_p158
  have hstep := st262_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p160 : ((50319770896659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT262 (i+1))
      = (∑ i ∈ Finset.range 159, stT262 (i+1)) + stT262 160 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 159
    simpa using h
  have hprev := st262_p159
  have hstep := st262_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p161 : ((51101942487809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT262 (i+1))
      = (∑ i ∈ Finset.range 160, stT262 (i+1)) + stT262 161 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 160
    simpa using h
  have hprev := st262_p160
  have hstep := st262_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p162 : ((50965931145859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT262 (i+1))
      = (∑ i ∈ Finset.range 161, stT262 (i+1)) + stT262 162 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 161
    simpa using h
  have hprev := st262_p161
  have hstep := st262_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p163 : ((392193299429/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT262 (i+1))
      = (∑ i ∈ Finset.range 162, stT262 (i+1)) + stT262 163 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 162
    simpa using h
  have hprev := st262_p162
  have hstep := st262_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p164 : ((12597927265597/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT262 (i+1))
      = (∑ i ∈ Finset.range 163, stT262 (i+1)) + stT262 164 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 163
    simpa using h
  have hprev := st262_p163
  have hstep := st262_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p165 : ((25571083949961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT262 (i+1))
      = (∑ i ∈ Finset.range 164, stT262 (i+1)) + stT262 165 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 164
    simpa using h
  have hprev := st262_p164
  have hstep := st262_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p166 : ((25463332458933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT262 (i+1))
      = (∑ i ∈ Finset.range 165, stT262 (i+1)) + stT262 166 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 165
    simpa using h
  have hprev := st262_p165
  have hstep := st262_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p167 : ((25091911254677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT262 (i+1))
      = (∑ i ∈ Finset.range 166, stT262 (i+1)) + stT262 167 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 166
    simpa using h
  have hprev := st262_p166
  have hstep := st262_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p168 : ((25197561498443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT262 (i+1))
      = (∑ i ∈ Finset.range 167, stT262 (i+1)) + stT262 168 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 167
    simpa using h
  have hprev := st262_p167
  have hstep := st262_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p169 : ((12784536140389/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT262 (i+1))
      = (∑ i ∈ Finset.range 168, stT262 (i+1)) + stT262 169 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 168
    simpa using h
  have hprev := st262_p168
  have hstep := st262_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p170 : ((50958390207541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT262 (i+1))
      = (∑ i ∈ Finset.range 169, stT262 (i+1)) + stT262 170 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 169
    simpa using h
  have hprev := st262_p169
  have hstep := st262_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p171 : ((50209239142021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT262 (i+1))
      = (∑ i ∈ Finset.range 170, stT262 (i+1)) + stT262 171 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 170
    simpa using h
  have hprev := st262_p170
  have hstep := st262_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p172 : ((50330136823573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT262 (i+1))
      = (∑ i ∈ Finset.range 171, stT262 (i+1)) + stT262 172 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 171
    simpa using h
  have hprev := st262_p171
  have hstep := st262_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p173 : ((51086009129433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT262 (i+1))
      = (∑ i ∈ Finset.range 172, stT262 (i+1)) + stT262 173 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 172
    simpa using h
  have hprev := st262_p172
  have hstep := st262_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p174 : ((25525322284591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT262 (i+1))
      = (∑ i ∈ Finset.range 173, stT262 (i+1)) + stT262 174 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 173
    simpa using h
  have hprev := st262_p173
  have hstep := st262_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p175 : ((25147436401207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT262 (i+1))
      = (∑ i ∈ Finset.range 174, stT262 (i+1)) + stT262 175 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 174
    simpa using h
  have hprev := st262_p174
  have hstep := st262_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p176 : ((50219090123091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT262 (i+1))
      = (∑ i ∈ Finset.range 175, stT262 (i+1)) + stT262 176 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 175
    simpa using h
  have hprev := st262_p175
  have hstep := st262_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p177 : ((10191518568227/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT262 (i+1))
      = (∑ i ∈ Finset.range 176, stT262 (i+1)) + stT262 177 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 176
    simpa using h
  have hprev := st262_p176
  have hstep := st262_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p178 : ((51165956462887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT262 (i+1))
      = (∑ i ∈ Finset.range 177, stT262 (i+1)) + stT262 178 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 177
    simpa using h
  have hprev := st262_p177
  have hstep := st262_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p179 : ((50473125894739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT262 (i+1))
      = (∑ i ∈ Finset.range 178, stT262 (i+1)) + stT262 179 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 178
    simpa using h
  have hprev := st262_p178
  have hstep := st262_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p180 : ((50118402775423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT262 (i+1))
      = (∑ i ∈ Finset.range 179, stT262 (i+1)) + stT262 180 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 179
    simpa using h
  have hprev := st262_p179
  have hstep := st262_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p181 : ((50725379628999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT262 (i+1))
      = (∑ i ∈ Finset.range 180, stT262 (i+1)) + stT262 181 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 180
    simpa using h
  have hprev := st262_p180
  have hstep := st262_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p182 : ((3201657379011/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT262 (i+1))
      = (∑ i ∈ Finset.range 181, stT262 (i+1)) + stT262 182 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 181
    simpa using h
  have hprev := st262_p181
  have hstep := st262_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p183 : ((25377075015811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT262 (i+1))
      = (∑ i ∈ Finset.range 182, stT262 (i+1)) + stT262 183 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 182
    simpa using h
  have hprev := st262_p182
  have hstep := st262_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p184 : ((12531419442353/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT262 (i+1))
      = (∑ i ∈ Finset.range 183, stT262 (i+1)) + stT262 184 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 183
    simpa using h
  have hprev := st262_p183
  have hstep := st262_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p185 : ((25205773676481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT262 (i+1))
      = (∑ i ∈ Finset.range 184, stT262 (i+1)) + stT262 185 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 184
    simpa using h
  have hprev := st262_p184
  have hstep := st262_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p186 : ((51123554466477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT262 (i+1))
      = (∑ i ∈ Finset.range 185, stT262 (i+1)) + stT262 186 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 185
    simpa using h
  have hprev := st262_p185
  have hstep := st262_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p187 : ((51068687053287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT262 (i+1))
      = (∑ i ∈ Finset.range 186, stT262 (i+1)) + stT262 187 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 186
    simpa using h
  have hprev := st262_p186
  have hstep := st262_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p188 : ((6292856848839/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT262 (i+1))
      = (∑ i ∈ Finset.range 187, stT262 (i+1)) + stT262 188 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 187
    simpa using h
  have hprev := st262_p187
  have hstep := st262_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p189 : ((5014230235711/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT262 (i+1))
      = (∑ i ∈ Finset.range 188, stT262 (i+1)) + stT262 189 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 188
    simpa using h
  have hprev := st262_p188
  have hstep := st262_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p190 : ((25394947803303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT262 (i+1))
      = (∑ i ∈ Finset.range 189, stT262 (i+1)) + stT262 190 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 189
    simpa using h
  have hprev := st262_p189
  have hstep := st262_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p191 : ((25617591523103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT262 (i+1))
      = (∑ i ∈ Finset.range 190, stT262 (i+1)) + stT262 191 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 190
    simpa using h
  have hprev := st262_p190
  have hstep := st262_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p192 : ((5076736900747/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT262 (i+1))
      = (∑ i ∈ Finset.range 191, stT262 (i+1)) + stT262 192 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 191
    simpa using h
  have hprev := st262_p191
  have hstep := st262_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p193 : ((25067030966991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT262 (i+1))
      = (∑ i ∈ Finset.range 192, stT262 (i+1)) + stT262 193 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 192
    simpa using h
  have hprev := st262_p192
  have hstep := st262_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p194 : ((25165750191991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT262 (i+1))
      = (∑ i ∈ Finset.range 193, stT262 (i+1)) + stT262 194 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 193
    simpa using h
  have hprev := st262_p193
  have hstep := st262_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p195 : ((25523250055299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT262 (i+1))
      = (∑ i ∈ Finset.range 194, stT262 (i+1)) + stT262 195 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 194
    simpa using h
  have hprev := st262_p194
  have hstep := st262_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p196 : ((6396419105361/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT262 (i+1))
      = (∑ i ∈ Finset.range 195, stT262 (i+1)) + stT262 196 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 195
    simpa using h
  have hprev := st262_p195
  have hstep := st262_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p197 : ((50518807066227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT262 (i+1))
      = (∑ i ∈ Finset.range 196, stT262 (i+1)) + stT262 197 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 196
    simpa using h
  have hprev := st262_p196
  have hstep := st262_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p198 : ((50084502415827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT262 (i+1))
      = (∑ i ∈ Finset.range 197, stT262 (i+1)) + stT262 198 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 197
    simpa using h
  have hprev := st262_p197
  have hstep := st262_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p199 : ((50520488332781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT262 (i+1))
      = (∑ i ∈ Finset.range 198, stT262 (i+1)) + stT262 199 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 198
    simpa using h
  have hprev := st262_p198
  have hstep := st262_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p200 : ((10234072800313/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT262 (i+1))
      = (∑ i ∈ Finset.range 199, stT262 (i+1)) + stT262 200 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 199
    simpa using h
  have hprev := st262_p199
  have hstep := st262_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p201 : ((10214251167021/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT262 (i+1))
      = (∑ i ∈ Finset.range 200, stT262 (i+1)) + stT262 201 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 200
    simpa using h
  have hprev := st262_p200
  have hstep := st262_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p202 : ((50373527249621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT262 (i+1))
      = (∑ i ∈ Finset.range 201, stT262 (i+1)) + stT262 202 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 201
    simpa using h
  have hprev := st262_p201
  have hstep := st262_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p203 : ((12523977563253/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT262 (i+1))
      = (∑ i ∈ Finset.range 202, stT262 (i+1)) + stT262 203 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 202
    simpa using h
  have hprev := st262_p202
  have hstep := st262_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p204 : ((6329485690809/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT262 (i+1))
      = (∑ i ∈ Finset.range 203, stT262 (i+1)) + stT262 204 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 203
    simpa using h
  have hprev := st262_p203
  have hstep := st262_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p205 : ((1600491228711/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT262 (i+1))
      = (∑ i ∈ Finset.range 204, stT262 (i+1)) + stT262 205 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 204
    simpa using h
  have hprev := st262_p204
  have hstep := st262_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p206 : ((318830329209/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT262 (i+1))
      = (∑ i ∈ Finset.range 205, stT262 (i+1)) + stT262 206 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 205
    simpa using h
  have hprev := st262_p205
  have hstep := st262_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p207 : ((12579446053017/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT262 (i+1))
      = (∑ i ∈ Finset.range 206, stT262 (i+1)) + stT262 207 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 206
    simpa using h
  have hprev := st262_p206
  have hstep := st262_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p208 : ((12525768870009/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT262 (i+1))
      = (∑ i ∈ Finset.range 207, stT262 (i+1)) + stT262 208 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 207
    simpa using h
  have hprev := st262_p207
  have hstep := st262_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p209 : ((25331191830649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT262 (i+1))
      = (∑ i ∈ Finset.range 208, stT262 (i+1)) + stT262 209 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 208
    simpa using h
  have hprev := st262_p208
  have hstep := st262_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p210 : ((51223323008433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT262 (i+1))
      = (∑ i ∈ Finset.range 209, stT262 (i+1)) + stT262 210 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 209
    simpa using h
  have hprev := st262_p209
  have hstep := st262_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p211 : ((10204561960207/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT262 (i+1))
      = (∑ i ∈ Finset.range 210, stT262 (i+1)) + stT262 211 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 210
    simpa using h
  have hprev := st262_p210
  have hstep := st262_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p212 : ((50336431245289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT262 (i+1))
      = (∑ i ∈ Finset.range 211, stT262 (i+1)) + stT262 212 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 211
    simpa using h
  have hprev := st262_p211
  have hstep := st262_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p213 : ((10017163851481/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT262 (i+1))
      = (∑ i ∈ Finset.range 212, stT262 (i+1)) + stT262 213 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 212
    simpa using h
  have hprev := st262_p212
  have hstep := st262_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p214 : ((5060060592977/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT262 (i+1))
      = (∑ i ∈ Finset.range 213, stT262 (i+1)) + stT262 214 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 213
    simpa using h
  have hprev := st262_p213
  have hstep := st262_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p215 : ((3199871884531/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT262 (i+1))
      = (∑ i ∈ Finset.range 214, stT262 (i+1)) + stT262 215 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 214
    simpa using h
  have hprev := st262_p214
  have hstep := st262_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p216 : ((6387161893581/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT262 (i+1))
      = (∑ i ∈ Finset.range 215, stT262 (i+1)) + stT262 216 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 215
    simpa using h
  have hprev := st262_p215
  have hstep := st262_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p217 : ((6304205676891/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT262 (i+1))
      = (∑ i ∈ Finset.range 216, stT262 (i+1)) + stT262 217 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 216
    simpa using h
  have hprev := st262_p216
  have hstep := st262_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p218 : ((25031669985957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT262 (i+1))
      = (∑ i ∈ Finset.range 217, stT262 (i+1)) + stT262 218 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 217
    simpa using h
  have hprev := st262_p217
  have hstep := st262_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p219 : ((50456306039683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT262 (i+1))
      = (∑ i ∈ Finset.range 218, stT262 (i+1)) + stT262 219 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 218
    simpa using h
  have hprev := st262_p218
  have hstep := st262_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p220 : ((51110582459233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT262 (i+1))
      = (∑ i ∈ Finset.range 219, stT262 (i+1)) + stT262 220 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 219
    simpa using h
  have hprev := st262_p219
  have hstep := st262_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p221 : ((51203797308961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT262 (i+1))
      = (∑ i ∈ Finset.range 220, stT262 (i+1)) + stT262 221 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 220
    simpa using h
  have hprev := st262_p220
  have hstep := st262_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p222 : ((2024947363933/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT262 (i+1))
      = (∑ i ∈ Finset.range 221, stT262 (i+1)) + stT262 222 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 221
    simpa using h
  have hprev := st262_p221
  have hstep := st262_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p223 : ((2003630074051/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT262 (i+1))
      = (∑ i ∈ Finset.range 222, stT262 (i+1)) + stT262 223 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 222
    simpa using h
  have hprev := st262_p222
  have hstep := st262_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p224 : ((50257290322831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT262 (i+1))
      = (∑ i ∈ Finset.range 223, stT262 (i+1)) + stT262 224 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 223
    simpa using h
  have hprev := st262_p223
  have hstep := st262_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p225 : ((50916258330529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT262 (i+1))
      = (∑ i ∈ Finset.range 224, stT262 (i+1)) + stT262 225 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 224
    simpa using h
  have hprev := st262_p224
  have hstep := st262_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p226 : ((51269975108599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT262 (i+1))
      = (∑ i ∈ Finset.range 225, stT262 (i+1)) + stT262 226 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 225
    simpa using h
  have hprev := st262_p225
  have hstep := st262_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p227 : ((50897361118723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT262 (i+1))
      = (∑ i ∈ Finset.range 226, stT262 (i+1)) + stT262 227 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 226
    simpa using h
  have hprev := st262_p226
  have hstep := st262_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p228 : ((50245392370573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT262 (i+1))
      = (∑ i ∈ Finset.range 227, stT262 (i+1)) + stT262 228 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 227
    simpa using h
  have hprev := st262_p227
  have hstep := st262_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p229 : ((50083590838423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT262 (i+1))
      = (∑ i ∈ Finset.range 228, stT262 (i+1)) + stT262 229 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 228
    simpa using h
  have hprev := st262_p228
  have hstep := st262_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p230 : ((50597722612023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT262 (i+1))
      = (∑ i ∈ Finset.range 229, stT262 (i+1)) + stT262 230 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 229
    simpa using h
  have hprev := st262_p229
  have hstep := st262_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p231 : ((51187200651453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT262 (i+1))
      = (∑ i ∈ Finset.range 230, stT262 (i+1)) + stT262 231 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 230
    simpa using h
  have hprev := st262_p230
  have hstep := st262_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p232 : ((5117331432197/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT262 (i+1))
      = (∑ i ∈ Finset.range 231, stT262 (i+1)) + stT262 232 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 231
    simpa using h
  have hprev := st262_p231
  have hstep := st262_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p233 : ((12643962238517/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT262 (i+1))
      = (∑ i ∈ Finset.range 232, stT262 (i+1)) + stT262 233 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 232
    simpa using h
  have hprev := st262_p232
  have hstep := st262_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p234 : ((2503775590987/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT262 (i+1))
      = (∑ i ∈ Finset.range 233, stT262 (i+1)) + stT262 234 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 233
    simpa using h
  have hprev := st262_p233
  have hstep := st262_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p235 : ((12558543248221/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT262 (i+1))
      = (∑ i ∈ Finset.range 234, stT262 (i+1)) + stT262 235 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 234
    simpa using h
  have hprev := st262_p234
  have hstep := st262_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p236 : ((12717609714157/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT262 (i+1))
      = (∑ i ∈ Finset.range 235, stT262 (i+1)) + stT262 236 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 235
    simpa using h
  have hprev := st262_p235
  have hstep := st262_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p237 : ((51276578626033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT262 (i+1))
      = (∑ i ∈ Finset.range 236, stT262 (i+1)) + stT262 237 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 236
    simpa using h
  have hprev := st262_p236
  have hstep := st262_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p238 : ((51007719163729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT262 (i+1))
      = (∑ i ∈ Finset.range 237, stT262 (i+1)) + stT262 238 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 237
    simpa using h
  have hprev := st262_p237
  have hstep := st262_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p239 : ((1573796357317/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT262 (i+1))
      = (∑ i ∈ Finset.range 238, stT262 (i+1)) + stT262 239 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 238
    simpa using h
  have hprev := st262_p238
  have hstep := st262_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p240 : ((5003990084903/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT262 (i+1))
      = (∑ i ∈ Finset.range 239, stT262 (i+1)) + stT262 240 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 239
    simpa using h
  have hprev := st262_p239
  have hstep := st262_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p241 : ((25193179110581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT262 (i+1))
      = (∑ i ∈ Finset.range 240, stT262 (i+1)) + stT262 241 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 240
    simpa using h
  have hprev := st262_p240
  have hstep := st262_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p242 : ((1020539765257/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT262 (i+1))
      = (∑ i ∈ Finset.range 241, stT262 (i+1)) + stT262 242 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 241
    simpa using h
  have hprev := st262_p241
  have hstep := st262_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p243 : ((1025633903927/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT262 (i+1))
      = (∑ i ∈ Finset.range 242, stT262 (i+1)) + stT262 243 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 242
    simpa using h
  have hprev := st262_p242
  have hstep := st262_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p244 : ((2035412345959/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT262 (i+1))
      = (∑ i ∈ Finset.range 243, stT262 (i+1)) + stT262 244 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 243
    simpa using h
  have hprev := st262_p243
  have hstep := st262_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p245 : ((50255437259167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT262 (i+1))
      = (∑ i ∈ Finset.range 244, stT262 (i+1)) + stT262 245 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 244
    simpa using h
  have hprev := st262_p244
  have hstep := st262_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p246 : ((25022840719757/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT262 (i+1))
      = (∑ i ∈ Finset.range 245, stT262 (i+1)) + stT262 246 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 245
    simpa using h
  have hprev := st262_p245
  have hstep := st262_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p247 : ((25234438554667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT262 (i+1))
      = (∑ i ∈ Finset.range 246, stT262 (i+1)) + stT262 247 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 246
    simpa using h
  have hprev := st262_p246
  have hstep := st262_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p248 : ((25544579539667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT262 (i+1))
      = (∑ i ∈ Finset.range 247, stT262 (i+1)) + stT262 248 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 247
    simpa using h
  have hprev := st262_p247
  have hstep := st262_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p249 : ((25638503139983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT262 (i+1))
      = (∑ i ∈ Finset.range 248, stT262 (i+1)) + stT262 249 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 248
    simpa using h
  have hprev := st262_p248
  have hstep := st262_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_p250 : ((25423135428127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT262 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT262 (i+1))
      = (∑ i ∈ Finset.range 249, stT262 (i+1)) + stT262 250 := by
    have h := Finset.sum_range_succ (fun i => stT262 (i+1)) 249
    simpa using h
  have hprev := st262_p249
  have hstep := st262_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st262_s250 :
    |Real.sin (((262 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))
      - ((366141/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 724977/1250000) (δ := 13253/1000000000) (ψ := -414889/500000) 262 230
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 262`** (evaluated boundary). -/
theorem station_262_sign : 0 < hardyG ((((262:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 262 250 (by norm_num) (by norm_num)
    ((-414889/500000 : ℚ) : ℝ)
  have hchain := st262_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT262 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((262 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-414889/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st262_c250
  have hsinb := abs_le.mp st262_s250
  have hbdy_lo : ((-3785456842739/85805312500000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((262 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-414889/500000 : ℚ) : ℝ))) / 2
          - ((((262:ℕ)):ℝ))
            * Real.sin (((262 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-414889/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((262:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((262:ℝ) * Real.log (250:ℝ) - ((-414889/500000 : ℚ) : ℝ))) / 2
        - ((262:ℝ)) * Real.sin ((262:ℝ) * Real.log (250:ℝ) - ((-414889/500000 : ℚ) : ℝ))
        ≥ ((-47882627/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((262:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-47882627/250000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-47882627/250000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-47882627/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((262:ℕ)):ℝ))+1) * (((((262:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((117512617453/78125000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((25423135428127/5000000000000 : ℚ) : ℝ) + ((-3785456842739/85805312500000 : ℚ) : ℝ)
      - ((117512617453/78125000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-414889/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((262:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-414889/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((262:ℕ)):ℝ)))).re
      - Real.sin ((-414889/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((262:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((262:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((262:ℕ)):ℝ))
      = (((((262:ℕ)):ℝ)) * (Real.log ((((262:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((262:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_262
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
  have hθwin : |(((-414889/500000 : ℚ) : ℝ) + ((57:ℤ)) * (2*Real.pi)) - theta ((((262:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((262:ℕ)):ℝ)))
    (φ := ((-414889/500000 : ℚ) : ℝ) + ((57:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-414889/500000 : ℚ)) : ℝ) 57).1,
    (cos_sin_shift (((-414889/500000 : ℚ)) : ℝ) 57).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_262_sign
end AxiomAudit
