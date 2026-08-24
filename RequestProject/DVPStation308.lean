import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 308` (rung-309; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT308 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((308 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-270827/250000 : ℚ) : ℝ))

theorem st308_c1 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((58551/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 270827/1000000) (δ := 1/1000000000) (ψ := -270827/250000) 308 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t1 : ((117077/250000 : ℚ) : ℝ) ≤ stT308 1 := by
  have hc : ((117077/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117077/250000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((117077/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c2 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((293143/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 295103/1250000) (δ := 15557/1000000000) (ψ := -270827/250000) 308 34
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t2 : ((2072480240231/5000000000000 : ℚ) : ℝ) ≤ stT308 2 := by
  have hc : ((293093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2072480240231/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((293093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c3 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((986603/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 204843/5000000) (δ := 7707/500000000) (ψ := -270827/250000) 308 54
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t3 : ((2847788521753/5000000000000 : ℚ) : ℝ) ≤ stT308 3 := by
  have hc : ((986503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2847788521753/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((986503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c4 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((692847/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2013417/10000000) (δ := 15513/1000000000) (ψ := -270827/250000) 308 68
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t4 : ((692747/2000000 : ℚ) : ℝ) ≤ stT308 4 := by
  have hc : ((692747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((692747/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((692747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c5 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((228419/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1046393/10000000) (δ := 7767/500000000) (ψ := -270827/250000) 308 79
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t5 : ((102140880119/250000000000 : ℚ) : ℝ) ≤ stT308 5 := by
  have hc : ((114197/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102140880119/250000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((114197/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c6 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((99969/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 62279/10000000) (δ := 15433/1000000000) (ψ := -270827/250000) 308 88
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t6 : ((204040409119/500000000000 : ℚ) : ℝ) ≤ stT308 6 := by
  have hc : ((99959/100000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204040409119/500000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((99959/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c7 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-928873/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1726347/2500000) (δ := 15491/1000000000) (ψ := -270827/250000) 308 96
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t7 : ((-702237630917/2000000000000 : ℚ) : ℝ) ≤ stT308 7 := by
  have hc : ((-928973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-702237630917/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-928973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c8 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((15721/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 166601/1000000) (δ := 15469/1000000000) (ψ := -270827/250000) 308 102
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t8 : ((55575043227/200000000000 : ℚ) : ℝ) ≤ stT308 8 := by
  have hc : ((15719/20000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55575043227/200000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((15719/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c9 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((727899/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1888859/10000000) (δ := 15577/1000000000) (ψ := -270827/250000) 308 108
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t9 : ((2425996424067/10000000000000 : ℚ) : ℝ) ≤ stT308 9 := by
  have hc : ((727799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2425996424067/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((727799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c10 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((120147/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 698909/10000000) (δ := 1549/100000000) (ψ := -270827/250000) 308 113
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t10 : ((759797132513/2500000000000 : ℚ) : ℝ) ≤ stT308 10 := by
  have hc : ((240269/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((759797132513/2500000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((240269/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c11 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-52121/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4452053/10000000) (δ := 15449/1000000000) (ψ := -270827/250000) 308 118
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t11 : ((-39306533661/625000000000 : ℚ) : ℝ) ≤ stT308 11 := by
  have hc : ((-26073/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39306533661/625000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-26073/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c12 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((993503/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35641/1250000) (δ := 15477/1000000000) (ψ := -270827/250000) 308 122
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t12 : ((2867707103653/10000000000000 : ℚ) : ℝ) ≤ stT308 12 := by
  have hc : ((993403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2867707103653/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((993403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c13 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((82891/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -742051/5000000) (δ := 7753/500000000) (ψ := -270827/250000) 308 126
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t13 : ((459740907/2000000000 : ℚ) : ℝ) ≤ stT308 13 := by
  have hc : ((82881/100000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((459740907/2000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((82881/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c14 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-38849/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1450559/2000000) (δ := 3107/200000000) (ψ := -270827/250000) 308 130
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t14 : ((-103839032889/400000000000 : ℚ) : ℝ) ≤ stT308 14 := by
  have hc : ((-38853/40000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103839032889/400000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-38853/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c15 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((87717/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -156519/1250000) (δ := 483/31250000) (ψ := -270827/250000) 308 133
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t15 : ((56614605379/250000000000 : ℚ) : ℝ) ≤ stT308 15 := by
  have hc : ((87707/100000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56614605379/250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((87707/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c16 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((432049/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1318603/10000000) (δ := 617/40000000) (ψ := -270827/250000) 308 136
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t16 : ((431999/2000000 : ℚ) : ℝ) ≤ stT308 16 := by
  have hc : ((431999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((431999/2000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((431999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c17 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((939283/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 175131/2000000) (δ := 969/62500000) (ψ := -270827/250000) 308 139
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t17 : ((569463281037/2500000000000 : ℚ) : ℝ) ≤ stT308 17 := by
  have hc : ((939183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((569463281037/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((939183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c18 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((39119/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2236267/10000000) (δ := 7791/500000000) (ψ := -270827/250000) 308 142
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t18 : ((184379224461/1250000000000 : ℚ) : ℝ) ≤ stT308 18 := by
  have hc : ((156451/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184379224461/1250000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((156451/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c19 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-998739/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1932103/2500000) (δ := 15543/1000000000) (ψ := -270827/250000) 308 145
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t19 : ((-1145747241281/5000000000000 : ℚ) : ℝ) ≤ stT308 19 := by
  have hc : ((-998839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1145747241281/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-998839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c20 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((247533/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 175751/5000000) (δ := 7723/500000000) (ψ := -270827/250000) 308 147
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t20 : ((138361117759/625000000000 : ℚ) : ℝ) ≤ stT308 20 := by
  have hc : ((61877/62500 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138361117759/625000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((61877/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c21 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-857719/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 650403/1000000) (δ := 15571/1000000000) (ψ := -270827/250000) 308 149
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t21 : ((-1871914607601/10000000000000 : ℚ) : ℝ) ≤ stT308 21 := by
  have hc : ((-857819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1871914607601/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-857819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c22 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-341947/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -239973/500000) (δ := 15493/1000000000) (ψ := -270827/250000) 308 152
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t22 : ((-91155867547/1250000000000 : ℚ) : ℝ) ≤ stT308 22 := by
  have hc : ((-342047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91155867547/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-342047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c23 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((175071/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1987501/10000000) (δ := 1937/125000000) (ψ := -270827/250000) 308 154
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t23 : ((22812257289/156250000000 : ℚ) : ℝ) ≤ stT308 23 := by
  have hc : ((87523/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22812257289/156250000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((87523/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c24 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((484081/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -126507/2000000) (δ := 7761/500000000) (ψ := -270827/250000) 308 156
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t24 : ((988023922471/5000000000000 : ℚ) : ℝ) ≤ stT308 24 := by
  have hc : ((484031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((988023922471/5000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((484031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c25 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((969843/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -307761/5000000) (δ := 15467/1000000000) (ψ := -270827/250000) 308 158
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t25 : ((969743/5000000 : ℚ) : ℝ) ≤ stT308 25 := by
  have hc : ((969743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((969743/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((969743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c26 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((185859/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1831509/10000000) (δ := 311/20000000) (ψ := -270827/250000) 308 160
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t26 : ((182225196637/1250000000000 : ℚ) : ℝ) ≤ stT308 26 := by
  have hc : ((92917/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182225196637/1250000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((92917/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c27 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-103977/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -837481/2000000) (δ := 7719/500000000) (ψ := -270827/250000) 308 162
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t27 : ((-200296290577/10000000000000 : ℚ) : ℝ) ≤ stT308 27 := by
  have hc : ((-104077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-200296290577/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-104077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c28 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-248713/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3800101/5000000) (δ := 15579/1000000000) (ψ := -270827/250000) 308 164
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t28 : ((-235035396687/1250000000000 : ℚ) : ℝ) ≤ stT308 28 := by
  have hc : ((-124369/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-235035396687/1250000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-124369/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c29 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((85837/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 742427/2000000) (δ := 15517/1000000000) (ψ := -270827/250000) 308 165
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t29 : ((159209579361/10000000000000 : ℚ) : ℝ) ≤ stT308 29 := by
  have hc : ((85737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159209579361/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((85737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c30 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((802183/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -399909/2500000) (δ := 31/2000000) (ψ := -270827/250000) 308 167
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t30 : ((1464395818503/10000000000000 : ℚ) : ℝ) ≤ stT308 30 := by
  have hc : ((802083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1464395818503/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((802083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c31 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-4997/5000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -388367/500000) (δ := 121/7812500) (ψ := -270827/250000) 308 169
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t31 : ((-1795155973/10000000000 : ℚ) : ℝ) ≤ stT308 31 := by
  have hc : ((-1999/2000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1795155973/10000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-1999/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c32 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((462743/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 242799/2500000) (δ := 7711/500000000) (ψ := -270827/250000) 308 170
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t32 : ((408966476919/2500000000000 : ℚ) : ℝ) ≤ stT308 32 := by
  have hc : ((462693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((408966476919/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((462693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c33 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-36167/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6750599/10000000) (δ := 15567/1000000000) (ψ := -270827/250000) 308 172
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t33 : ((-62965644867/400000000000 : ℚ) : ℝ) ≤ stT308 33 := by
  have hc : ((-36171/40000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62965644867/400000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-36171/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c34 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((977759/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66031/1250000) (δ := 15459/1000000000) (ψ := -270827/250000) 308 173
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t34 : ((335334104023/2000000000000 : ℚ) : ℝ) ≤ stT308 34 := by
  have hc : ((977659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((335334104023/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((977659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c35 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-959569/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 357033/500000) (δ := 15451/1000000000) (ψ := -270827/250000) 308 174
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t35 : ((-1622137147721/10000000000000 : ℚ) : ℝ) ≤ stT308 35 := by
  have hc : ((-959669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1622137147721/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-959669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c36 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((511841/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1291837/5000000) (δ := 7769/500000000) (ψ := -270827/250000) 308 176
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t36 : ((426450662753/5000000000000 : ℚ) : ℝ) ≤ stT308 36 := by
  have hc : ((511741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((426450662753/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((511741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c37 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((108417/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2805593/10000000) (δ := 15431/1000000000) (ψ := -270827/250000) 308 177
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t37 : ((22274406961/312500000000 : ℚ) : ℝ) ≤ stT308 37 := by
  have hc : ((13549/31250 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22274406961/312500000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((13549/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c38 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-498033/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 477009/625000) (δ := 15479/1000000000) (ψ := -270827/250000) 308 178
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t38 : ((-161599542769/1000000000000 : ℚ) : ℝ) ≤ stT308 38 := by
  have hc : ((-498083/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161599542769/1000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-498083/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c39 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((11541/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -472831/1250000) (δ := 15509/1000000000) (ψ := -270827/250000) 308 180
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t39 : ((18448358401/2000000000000 : ℚ) : ℝ) ≤ stT308 39 := by
  have hc : ((11521/200000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18448358401/2000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((11521/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c40 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((999999/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 819/2000000) (δ := 7701/500000000) (ψ := -270827/250000) 308 181
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t40 : ((790489152531/5000000000000 : ℚ) : ℝ) ≤ stT308 40 := by
  have hc : ((999899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((790489152531/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((999899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c41 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((122259/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1654717/5000000) (δ := 3877/250000000) (ψ := -270827/250000) 308 182
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t41 : ((190858317033/5000000000000 : ℚ) : ℝ) ≤ stT308 41 := by
  have hc : ((122209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190858317033/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((122209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c42 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-194559/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3078311/5000000) (δ := 3897/250000000) (ψ := -270827/250000) 308 183
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t42 : ((-18765607991/156250000000 : ℚ) : ℝ) ≤ stT308 42 := by
  have hc : ((-24323/31250 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18765607991/156250000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-24323/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c43 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-959587/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7140819/10000000) (δ := 1543/100000000) (ψ := -270827/250000) 308 185
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t43 : ((-731754619691/5000000000000 : ℚ) : ℝ) ≤ stT308 43 := by
  have hc : ((-959687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-731754619691/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-959687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c44 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-468817/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5146867/10000000) (δ := 15537/1000000000) (ψ := -270827/250000) 308 186
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t44 : ((-706919105769/10000000000000 : ℚ) : ℝ) ≤ stT308 44 := by
  have hc : ((-468917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-706919105769/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-468917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c45 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((149919/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -142031/400000) (δ := 15559/1000000000) (ψ := -270827/250000) 308 187
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t45 : ((223336831309/10000000000000 : ℚ) : ℝ) ≤ stT308 45 := by
  have hc : ((149819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((223336831309/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((149819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c46 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((148657/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -466997/2000000) (δ := 3863/250000000) (ψ := -270827/250000) 308 188
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t46 : ((27393230601/312500000000 : ℚ) : ℝ) ≤ stT308 46 := by
  have hc : ((18579/31250 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27393230601/312500000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((18579/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c47 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((414567/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1483097/10000000) (δ := 7729/500000000) (ψ := -270827/250000) 308 189
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t47 : ((604634807533/5000000000000 : ℚ) : ℝ) ≤ stT308 47 := by
  have hc : ((414517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((604634807533/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((414517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c48 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((231039/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -489971/5000000) (δ := 7783/500000000) (ψ := -270827/250000) 308 190
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t48 : ((1333759329/10000000000 : ℚ) : ℝ) ≤ stT308 48 := by
  have hc : ((115507/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1333759329/10000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((115507/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c49 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((947827/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -405561/5000000) (δ := 1553/100000000) (ψ := -270827/250000) 308 191
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t49 : ((1353895308117/10000000000000 : ℚ) : ℝ) ≤ stT308 49 := by
  have hc : ((947727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1353895308117/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((947727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c50 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((463367/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -962929/10000000) (δ := 15423/1000000000) (ψ := -270827/250000) 308 192
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t50 : ((655228924521/5000000000000 : ℚ) : ℝ) ≤ stT308 50 := by
  have hc : ((463317/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((655228924521/5000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((463317/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c51 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((210589/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -142289/1000000) (δ := 15487/1000000000) (ψ := -270827/250000) 308 193
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t51 : ((1842803487/15625000000 : ℚ) : ℝ) ≤ stT308 51 := by
  have hc : ((52641/62500 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1842803487/15625000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((52641/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c52 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((643629/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -544729/2500000) (δ := 7797/500000000) (ψ := -270827/250000) 308 194
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t52 : ((3569655363/40000000000 : ℚ) : ℝ) ≤ stT308 52 := by
  have hc : ((643529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3569655363/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((643529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c53 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((69783/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1609883/5000000) (δ := 15501/1000000000) (ψ := -270827/250000) 308 195
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t53 : ((9581993759/250000000000 : ℚ) : ℝ) ≤ stT308 53 := by
  have hc : ((34879/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9581993759/250000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((34879/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c54 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-12037/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1133703/2500000) (δ := 15409/1000000000) (ψ := -270827/250000) 308 196
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t54 : ((-2048386347/62500000000 : ℚ) : ℝ) ≤ stT308 54 := by
  have hc : ((-6021/25000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2048386347/62500000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-6021/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c55 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-767409/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -382123/625000) (δ := 3879/250000000) (ψ := -270827/250000) 308 197
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t55 : ((-2587272839/25000000000 : ℚ) : ℝ) ≤ stT308 55 := by
  have hc : ((-767509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2587272839/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-767509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c56 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-499649/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7760277/10000000) (δ := 3879/250000000) (ψ := -270827/250000) 308 197
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t56 : ((-667751271593/5000000000000 : ℚ) : ℝ) ≤ stT308 56 := by
  have hc : ((-499699/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-667751271593/5000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-499699/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c57 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-129089/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1136201/2000000) (δ := 779/50000000) (ψ := -270827/250000) 308 198
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t57 : ((-171009131097/2000000000000 : ℚ) : ℝ) ≤ stT308 57 := by
  have hc : ((-129109/200000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171009131097/2000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-129109/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c58 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((111507/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 420591/1250000) (δ := 15473/1000000000) (ψ := -270827/250000) 308 199
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t58 : ((18293771781/625000000000 : ℚ) : ℝ) ≤ stT308 58 := by
  have hc : ((111457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18293771781/625000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((111457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c59 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((946759/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 819453/10000000) (δ := 15437/1000000000) (ψ := -270827/250000) 308 200
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t59 : ((1232444938851/10000000000000 : ℚ) : ℝ) ≤ stT308 59 := by
  have hc : ((946659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1232444938851/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((946659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c60 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((142349/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1947043/10000000) (δ := 3109/200000000) (ψ := -270827/250000) 308 201
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t60 : ((91872942513/1000000000000 : ℚ) : ℝ) ≤ stT308 60 := by
  have hc : ((142329/200000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91872942513/1000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((142329/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c61 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-194793/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2463723/5000000) (δ := 15551/1000000000) (ψ := -270827/250000) 308 202
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t61 : ((-249470937067/5000000000000 : ℚ) : ℝ) ≤ stT308 61 := by
  have hc : ((-194843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-249470937067/5000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-194843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c62 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-497281/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7593139/10000000) (δ := 15551/1000000000) (ψ := -270827/250000) 308 202
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t62 : ((-315805682331/2500000000000 : ℚ) : ℝ) ≤ stT308 62 := by
  have hc : ((-497331/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-315805682331/2500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-497331/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c63 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-111167/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1051371/2500000) (δ := 3861/250000000) (ψ := -270827/250000) 308 203
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t63 : ((-70091645247/5000000000000 : ℚ) : ℝ) ≤ stT308 63 := by
  have hc : ((-111267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70091645247/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-111267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c64 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((12113/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19491/312500) (δ := 7733/500000000) (ψ := -270827/250000) 308 204
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t64 : ((48447/400000 : ℚ) : ℝ) ≤ stT308 64 := by
  have hc : ((48447/50000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48447/400000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((48447/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c65 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((307333/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3146017/10000000) (δ := 15573/1000000000) (ψ := -270827/250000) 308 205
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t65 : ((381075529851/10000000000000 : ℚ) : ℝ) ≤ stT308 65 := by
  have hc : ((307233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((381075529851/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((307233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c66 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-954627/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3549003/5000000) (δ := 15523/1000000000) (ψ := -270827/250000) 308 206
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t66 : ((-235037557041/2000000000000 : ℚ) : ℝ) ≤ stT308 66 := by
  have hc : ((-954727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-235037557041/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-954727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c67 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-219863/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4481177/10000000) (δ := 15523/1000000000) (ψ := -270827/250000) 308 206
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t67 : ((-53745539457/2000000000000 : ℚ) : ℝ) ≤ stT308 67 := by
  have hc : ((-219963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53745539457/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-219963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c68 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((199477/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 180841/10000000) (δ := 3083/200000000) (ψ := -270827/250000) 308 207
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t68 : ((120938557923/1000000000000 : ℚ) : ℝ) ≤ stT308 68 := by
  have hc : ((199457/200000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120938557923/1000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((199457/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c69 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-143129/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2143023/5000000) (δ := 3099/200000000) (ψ := -270827/250000) 308 208
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t69 : ((-172427520711/10000000000000 : ℚ) : ℝ) ≤ stT308 69 := by
  have hc : ((-143229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172427520711/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-143229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c70 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-911331/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6793253/10000000) (δ := 3099/200000000) (ψ := -270827/250000) 308 208
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t70 : ((-1089368762699/10000000000000 : ℚ) : ℝ) ≤ stT308 70 := by
  have hc : ((-911431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1089368762699/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-911431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c71 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((694571/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2007431/10000000) (δ := 15601/1000000000) (ψ := -270827/250000) 308 209
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t71 : ((824184987851/10000000000000 : ℚ) : ℝ) ≤ stT308 71 := by
  have hc : ((694471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((824184987851/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((694471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c72 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((387911/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2931081/10000000) (δ := 7747/500000000) (ψ := -270827/250000) 308 210
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t72 : ((457039529421/10000000000000 : ℚ) : ℝ) ≤ stT308 72 := by
  have hc : ((387811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((457039529421/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((387811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c73 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-997843/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 48061/62500) (δ := 7747/500000000) (ψ := -270827/250000) 308 210
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t73 : ((-292001115629/2500000000000 : ℚ) : ℝ) ≤ stT308 73 := by
  have hc : ((-997943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-292001115629/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-997943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c74 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((277163/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2458109/10000000) (δ := 1927/125000000) (ψ := -270827/250000) 308 211
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t74 : ((80534302947/1250000000000 : ℚ) : ℝ) ≤ stT308 74 := by
  have hc : ((277113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80534302947/1250000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((277113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c75 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((15767/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2914067/10000000) (δ := 3881/250000000) (ψ := -270827/250000) 308 212
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t75 : ((182015361/4000000000 : ℚ) : ℝ) ≤ stT308 75 := by
  have hc : ((15763/40000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182015361/4000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((15763/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c76 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-974189/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7284737/10000000) (δ := 3881/250000000) (ψ := -270827/250000) 308 212
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t76 : ((-1117586451831/10000000000000 : ℚ) : ℝ) ≤ stT308 76 := by
  have hc : ((-974289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1117586451831/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-974289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c77 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((791879/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 164229/1000000) (δ := 3893/250000000) (ψ := -270827/250000) 308 213
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t77 : ((180463061459/2000000000000 : ℚ) : ℝ) ≤ stT308 77 := by
  have hc : ((791779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180463061459/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((791779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c78 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-5071/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -826011/2000000) (δ := 3093/200000000) (ψ := -270827/250000) 308 214
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t78 : ((-11497716951/1250000000000 : ℚ) : ℝ) ≤ stT308 78 := by
  have hc : ((-20309/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11497716951/1250000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-20309/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c79 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-25793/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 227159/400000) (δ := 3093/200000000) (ψ := -270827/250000) 308 214
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t79 : ((-906996723/12500000000 : ℚ) : ℝ) ≤ stT308 79 := by
  have hc : ((-25797/40000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-906996723/12500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-25797/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c80 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((495293/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21457/625000) (δ := 3089/200000000) (ψ := -270827/250000) 308 215
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t80 : ((553698017019/5000000000000 : ℚ) : ℝ) ≤ stT308 80 := by
  have hc : ((495243/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((553698017019/5000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((495243/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c81 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-426989/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -129719/200000) (δ := 243/15625000) (ψ := -270827/250000) 308 216
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t81 : ((-59311019671/625000000000 : ℚ) : ℝ) ≤ stT308 81 := by
  have hc : ((-427039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59311019671/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-427039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c82 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((47059/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2962027/10000000) (δ := 243/15625000) (ψ := -270827/250000) 308 216
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t82 : ((20781662259/500000000000 : ℚ) : ℝ) ≤ stT308 82 := by
  have hc : ((94093/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20781662259/500000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((94093/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c83 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((204363/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3412459/10000000) (δ := 1943/125000000) (ψ := -270827/250000) 308 217
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t83 : ((112103823923/5000000000000 : ℚ) : ℝ) ≤ stT308 83 := by
  have hc : ((204263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112103823923/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((204263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c84 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-683739/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5809177/10000000) (δ := 30859/1000000000) (ψ := -270827/250000) 308 217
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t84 : ((-74612989451/1000000000000 : ℚ) : ℝ) ≤ stT308 84 := by
  have hc : ((-683839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74612989451/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-683839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c85 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((19019/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -39313/500000) (δ := 3859/250000000) (ψ := -270827/250000) 308 218
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t85 : ((5156706771/50000000000 : ℚ) : ℝ) ≤ stT308 85 := by
  have hc : ((19017/20000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5156706771/50000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((19017/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c86 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-989321/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7488303/10000000) (δ := 7737/500000000) (ψ := -270827/250000) 308 219
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t86 : ((-133365046011/1250000000000 : ℚ) : ℝ) ≤ stT308 86 := by
  have hc : ((-989421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133365046011/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-989421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c87 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((168871/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 141359/1000000) (δ := 7737/500000000) (ψ := -270827/250000) 308 219
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t87 : ((11314198957/125000000000 : ℚ) : ℝ) ≤ stT308 87 := by
  have hc : ((168851/200000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11314198957/125000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((168851/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c88 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-73331/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2747137/5000000) (δ := 15581/1000000000) (ψ := -270827/250000) 308 220
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t88 : ((-39092232187/625000000000 : ℚ) : ℝ) ≤ stT308 88 := by
  have hc : ((-146687/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39092232187/625000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-146687/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c89 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((71071/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3206341/10000000) (δ := 15581/1000000000) (ψ := -270827/250000) 308 220
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t89 : ((37654273431/1250000000000 : ℚ) : ℝ) ≤ stT308 89 := by
  have hc : ((35523/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37654273431/1250000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((35523/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c90 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((11523/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1949091/5000000) (δ := 3103/200000000) (ψ := -270827/250000) 308 221
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t90 : ((3010223229/2500000000000 : ℚ) : ℝ) ≤ stT308 90 := by
  have hc : ((11423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3010223229/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((11423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c91 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-33737/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4610203/10000000) (δ := 3861/125000000) (ψ := -270827/250000) 308 221
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t91 : ((-14151637843/500000000000 : ℚ) : ℝ) ≤ stT308 91 := by
  have hc : ((-67499/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14151637843/500000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-67499/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c92 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((59691/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -335299/1250000) (δ := 963/62500000) (ψ := -270827/250000) 308 222
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t92 : ((31109566551/625000000000 : ℚ) : ℝ) ≤ stT308 92 := by
  have hc : ((119357/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31109566551/625000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((119357/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c93 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-12669/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5642001/10000000) (δ := 963/62500000) (ψ := -270827/250000) 308 222
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t93 : ((-1642402349/25000000000 : ℚ) : ℝ) ≤ stT308 93 := by
  have hc : ((-12671/20000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1642402349/25000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-12671/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c94 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((185921/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1830581/10000000) (δ := 15503/1000000000) (ψ := -270827/250000) 308 223
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t94 : ((23967129777/312500000000 : ℚ) : ℝ) ≤ stT308 94 := by
  have hc : ((23237/31250 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23967129777/312500000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((23237/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c95 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-10213/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1579409/2500000) (δ := 15503/1000000000) (ψ := -270827/250000) 308 223
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t95 : ((-41918424003/500000000000 : ℚ) : ℝ) ≤ stT308 95 := by
  have hc : ((-40857/50000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41918424003/500000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-40857/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c96 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((215579/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1327427/10000000) (δ := 15593/1000000000) (ψ := -270827/250000) 308 224
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t96 : ((5499968087/62500000000 : ℚ) : ℝ) ≤ stT308 96 := by
  have hc : ((107777/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5499968087/62500000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((107777/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c97 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-177323/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6651929/10000000) (δ := 15593/1000000000) (ψ := -270827/250000) 308 224
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t97 : ((-180064683021/2000000000000 : ℚ) : ℝ) ≤ stT308 97 := by
  have hc : ((-177343/200000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180064683021/2000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-177343/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c98 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((894533/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1158529/10000000) (δ := 7743/500000000) (ψ := -270827/250000) 308 225
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t98 : ((112939160477/1250000000000 : ℚ) : ℝ) ≤ stT308 98 := by
  have hc : ((894433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112939160477/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((894433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c99 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-887887/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6658819/10000000) (δ := 7743/500000000) (ψ := -270827/250000) 308 225
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t99 : ((-446230339253/5000000000000 : ℚ) : ℝ) ≤ stT308 99 := by
  have hc : ((-887987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-446230339253/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-887987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c100 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((432871/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1310413/10000000) (δ := 241/15625000) (ψ := -270827/250000) 308 226
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t100 : ((432820567179/5000000000000 : ℚ) : ℝ) ≤ stT308 100 := by
  have hc : ((432821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((432820567179/5000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((432821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c101 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-824751/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1270279/2000000) (δ := 241/15625000) (ψ := -270827/250000) 308 226
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t101 : ((-410379044669/5000000000000 : ℚ) : ℝ) ≤ stT308 101 := by
  have hc : ((-824851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-410379044669/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-824851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c102 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((759587/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1770297/10000000) (δ := 15531/1000000000) (ψ := -270827/250000) 308 227
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t102 : ((752003774589/10000000000000 : ℚ) : ℝ) ≤ stT308 102 := by
  have hc : ((759487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((752003774589/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((759487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c103 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-41491/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57419/100000) (δ := 15531/1000000000) (ψ := -270827/250000) 308 227
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t103 : ((-16355394137/250000000000 : ℚ) : ℝ) ≤ stT308 103 := by
  have hc : ((-165989/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16355394137/250000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-165989/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c104 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((265693/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2526401/10000000) (δ := 3113/200000000) (ψ := -270827/250000) 308 228
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t104 : ((13024210647/250000000000 : ℚ) : ℝ) ≤ stT308 104 := by
  have hc : ((265643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13024210647/250000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((265643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c105 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-357929/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2421057/5000000) (δ := 3113/200000000) (ψ := -270827/250000) 308 228
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t105 : ((-349400859129/10000000000000 : ℚ) : ℝ) ≤ stT308 105 := by
  have hc : ((-358029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-349400859129/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-358029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c106 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((717/5000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14269/40000) (δ := 15457/1000000000) (ψ := -270827/250000) 308 229
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t106 : ((278370281/20000000000 : ℚ) : ℝ) ≤ stT308 106 := by
  have hc : ((1433/10000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((278370281/20000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((1433/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c107 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((52721/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 228931/625000) (δ := 15457/1000000000) (ψ := -270827/250000) 308 229
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t107 : ((3182434491/312500000000 : ℚ) : ℝ) ≤ stT308 107 := by
  have hc : ((52671/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3182434491/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((52671/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c108 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-186431/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4882219/10000000) (δ := 15453/1000000000) (ψ := -270827/250000) 308 230
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t108 : ((-179441528731/5000000000000 : ℚ) : ℝ) ≤ stT308 108 := by
  have hc : ((-186481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179441528731/5000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-186481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c109 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((632651/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2214563/10000000) (δ := 15453/1000000000) (ψ := -270827/250000) 308 230
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t109 : ((302936897063/5000000000000 : ℚ) : ℝ) ≤ stT308 109 := by
  have hc : ((632551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((302936897063/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((632551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c110 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-424411/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51691/80000) (δ := 389/25000000) (ψ := -270827/250000) 308 231
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t110 : ((-404707858443/5000000000000 : ℚ) : ℝ) ≤ stT308 110 := by
  have hc : ((-424461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-404707858443/5000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-424461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c111 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((979503/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 63381/1250000) (δ := 389/25000000) (ψ := -270827/250000) 308 231
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t111 : ((929607213271/10000000000000 : ℚ) : ℝ) ≤ stT308 111 := by
  have hc : ((979403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((929607213271/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((979403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c112 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-492237/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 741287/1000000) (δ := 389/25000000) (ψ := -270827/250000) 308 231
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t112 : ((-29072993359/312500000000 : ℚ) : ℝ) ≤ stT308 112 := by
  have hc : ((-492287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29072993359/312500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-492287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c113 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((836339/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -362641/2500000) (δ := 971/62500000) (ψ := -270827/250000) 308 232
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t113 : ((9833334401/125000000000 : ℚ) : ℝ) ≤ stT308 113 := by
  have hc : ((836239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9833334401/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((836239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c114 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-33339/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2666799/5000000) (δ := 971/62500000) (ψ := -270827/250000) 308 232
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t114 : ((-62461388633/1250000000000 : ℚ) : ℝ) ≤ stT308 114 := by
  have hc : ((-133381/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62461388633/1250000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-133381/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c115 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((55401/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -456177/1250000) (δ := 15429/1000000000) (ψ := -270827/250000) 308 233
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t115 : ((6451878613/625000000000 : ℚ) : ℝ) ≤ stT308 115 := by
  have hc : ((55351/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6451878613/625000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((55351/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c116 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((4449/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 754311/2500000) (δ := 15429/1000000000) (ψ := -270827/250000) 308 233
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t116 : ((4129629129/125000000000 : ℚ) : ℝ) ≤ stT308 116 := by
  have hc : ((17791/50000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4129629129/125000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((17791/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c117 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-379469/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6081193/10000000) (δ := 7741/500000000) (ψ := -270827/250000) 308 234
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t117 : ((-350865695019/5000000000000 : ℚ) : ℝ) ≤ stT308 117 := by
  have hc : ((-379519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-350865695019/5000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-379519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c118 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((982227/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 236023/5000000) (δ := 7741/500000000) (ψ := -270827/250000) 308 234
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t118 : ((452060290449/5000000000000 : ℚ) : ℝ) ≤ stT308 118 := by
  have hc : ((982127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((452060290449/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((982127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c119 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-234531/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3484961/5000000) (δ := 7741/500000000) (ψ := -270827/250000) 308 234
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t119 : ((-53754312661/625000000000 : ℚ) : ℝ) ≤ stT308 119 := by
  have hc : ((-58639/62500 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53754312661/625000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-58639/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c120 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((121517/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -45889/200000) (δ := 15589/1000000000) (ψ := -270827/250000) 308 235
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t120 : ((11091096639/200000000000 : ℚ) : ℝ) ≤ stT308 120 := by
  have hc : ((121497/200000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11091096639/200000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((121497/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c121 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-67403/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2047813/5000000) (δ := 15589/1000000000) (ψ := -270827/250000) 308 235
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t121 : ((-61366369773/10000000000000 : ℚ) : ℝ) ≤ stT308 121 := by
  have hc : ((-67503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61366369773/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-67503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c122 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-256701/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5274853/10000000) (δ := 15507/1000000000) (ψ := -270827/250000) 308 236
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t122 : ((-116225785929/2500000000000 : ℚ) : ℝ) ≤ stT308 122 := by
  have hc : ((-256751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116225785929/2500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-256751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c123 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((229839/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126361/1250000) (δ := 15507/1000000000) (ψ := -270827/250000) 308 236
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t123 : ((103608079783/1250000000000 : ℚ) : ℝ) ≤ stT308 123 := by
  have hc : ((114907/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103608079783/1250000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((114907/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c124 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-242637/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1811433/2500000) (δ := 15507/1000000000) (ψ := -270827/250000) 308 236
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t124 : ((-108958513937/1250000000000 : ℚ) : ℝ) ≤ stT308 124 := by
  have hc : ((-121331/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108958513937/1250000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-121331/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c125 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((38311/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2277437/10000000) (δ := 15403/1000000000) (ψ := -270827/250000) 308 237
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t125 : ((137043210513/2500000000000 : ℚ) : ℝ) ≤ stT308 125 := by
  have hc : ((153219/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137043210513/2500000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((153219/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c126 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((13781/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3858077/10000000) (δ := 15403/1000000000) (ψ := -270827/250000) 308 237
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t126 : ((1223253597/500000000000 : ℚ) : ℝ) ≤ stT308 126 := by
  have hc : ((13731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1223253597/500000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((13731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c127 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-167533/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5762959/10000000) (δ := 1551/100000000) (ψ := -270827/250000) 308 238
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t127 : ((-74341882103/1250000000000 : ℚ) : ℝ) ≤ stT308 127 := by
  have hc : ((-83779/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74341882103/1250000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-83779/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c128 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((993899/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55261/2000000) (δ := 1551/100000000) (ψ := -270827/250000) 308 238
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t128 : ((878402041517/10000000000000 : ℚ) : ℝ) ≤ stT308 128 := by
  have hc : ((993799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((878402041517/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((993799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c129 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-402787/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6268599/10000000) (δ := 1551/100000000) (ψ := -270827/250000) 308 238
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t129 : ((-354678239487/5000000000000 : ℚ) : ℝ) ≤ stT308 129 := by
  have hc : ((-402837/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-354678239487/5000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-402837/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c130 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((86279/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -139737/400000) (δ := 7793/500000000) (ψ := -270827/250000) 308 239
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t130 : ((37813917141/2500000000000 : ℚ) : ℝ) ≤ stT308 130 := by
  have hc : ((86229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37813917141/2500000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((86229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c131 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((571221/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75219/312500) (δ := 7793/500000000) (ψ := -270827/250000) 308 239
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t131 : ((62373837773/1250000000000 : ℚ) : ℝ) ≤ stT308 131 := by
  have hc : ((571121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62373837773/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((571121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c132 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-39467/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7445413/10000000) (δ := 7739/500000000) (ψ := -270827/250000) 308 240
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t132 : ((-34355124219/400000000000 : ℚ) : ℝ) ≤ stT308 132 := by
  have hc : ((-39471/40000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34355124219/400000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-39471/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c133 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((793883/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1634069/10000000) (δ := 7739/500000000) (ψ := -270827/250000) 308 240
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t133 : ((688296383347/10000000000000 : ℚ) : ℝ) ≤ stT308 133 := by
  have hc : ((793783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((688296383347/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((793783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c134 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-41301/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1033433/2500000) (δ := 1237/40000000) (ψ := -270827/250000) 308 240
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t134 : ((-35721847019/5000000000000 : ℚ) : ℝ) ≤ stT308 134 := by
  have hc : ((-41351/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35721847019/5000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-41351/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c135 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-86921/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -146233/250000) (δ := 1929/125000000) (ψ := -270827/250000) 308 241
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t135 : ((-149640893821/2500000000000 : ℚ) : ℝ) ≤ stT308 135 := by
  have hc : ((-173867/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149640893821/2500000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-173867/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c136 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((997779/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -166643/10000000) (δ := 1929/125000000) (ψ := -270827/250000) 308 241
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t136 : ((213875440267/2500000000000 : ℚ) : ℝ) ≤ stT308 136 := by
  have hc : ((997679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213875440267/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((997679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c137 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-580209/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2737227/5000000) (δ := 1929/125000000) (ψ := -270827/250000) 308 241
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t137 : ((-247895818311/5000000000000 : ℚ) : ℝ) ≤ stT308 137 := by
  have hc : ((-580309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-247895818311/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-580309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c138 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-278869/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -463353/1000000) (δ := 15539/1000000000) (ψ := -270827/250000) 308 242
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t138 : ((-237474314033/10000000000000 : ℚ) : ℝ) ≤ stT308 138 := by
  have hc : ((-278969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237474314033/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-278969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c139 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((116521/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 926101/10000000) (δ := 15539/1000000000) (ψ := -270827/250000) 308 242
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t139 : ((49410555799/625000000000 : ℚ) : ℝ) ≤ stT308 139 := by
  have hc : ((233017/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49410555799/625000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((233017/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c140 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-422761/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3222923/5000000) (δ := 15539/1000000000) (ψ := -270827/250000) 308 242
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t140 : ((-71468166141/1000000000000 : ℚ) : ℝ) ≤ stT308 140 := by
  have hc : ((-422811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71468166141/1000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-422811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c141 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((14519/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -94543/250000) (δ := 15557/1000000000) (ψ := -270827/250000) 308 243
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t141 : ((6103068297/1250000000000 : ℚ) : ℝ) ≤ stT308 141 := by
  have hc : ((7247/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6103068297/1250000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((7247/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c142 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((98441/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 207503/1250000) (δ := 15557/1000000000) (ψ := -270827/250000) 308 243
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t142 : ((165198654117/2500000000000 : ℚ) : ℝ) ≤ stT308 142 := by
  have hc : ((196857/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165198654117/2500000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((196857/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c143 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-237609/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 882947/1250000) (δ := 15557/1000000000) (ψ := -270827/250000) 308 243
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t143 : ((-99359884531/1250000000000 : ℚ) : ℝ) ≤ stT308 143 := by
  have hc : ((-118817/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99359884531/1250000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-118817/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c144 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((32059/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -655713/2000000) (δ := 309/20000000) (ψ := -270827/250000) 308 244
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t144 : ((53410811969/2500000000000 : ℚ) : ℝ) ≤ stT308 144 := by
  have hc : ((64093/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53410811969/2500000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((64093/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c145 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((682157/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102511/500000) (δ := 309/20000000) (ψ := -270827/250000) 308 244
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t145 : ((283208481939/5000000000000 : ℚ) : ℝ) ≤ stT308 145 := by
  have hc : ((682057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((283208481939/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((682057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c146 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-244783/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7342353/10000000) (δ := 309/20000000) (ψ := -270827/250000) 308 244
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t146 : ((-12662785603/156250000000 : ℚ) : ℝ) ≤ stT308 146 := by
  have hc : ((-30601/31250 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12662785603/156250000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-30601/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c147 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((321137/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3109667/10000000) (δ := 773/50000000) (ψ := -270827/250000) 308 245
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t147 : ((132393411541/5000000000000 : ℚ) : ℝ) ≤ stT308 147 := by
  have hc : ((321037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132393411541/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((321037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c148 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((664269/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1055351/5000000) (δ := 773/50000000) (ψ := -270827/250000) 308 245
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t148 : ((272971466493/5000000000000 : ℚ) : ℝ) ≤ stT308 148 := by
  have hc : ((664169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272971466493/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((664169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c149 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-121899/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7295959/10000000) (δ := 773/50000000) (ψ := -270827/250000) 308 245
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t149 : ((-6242112623/78125000000 : ℚ) : ℝ) ≤ stT308 149 := by
  have hc : ((-243823/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6242112623/78125000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-243823/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c150 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((65761/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3261551/10000000) (δ := 973/62500000) (ψ := -270827/250000) 308 246
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t150 : ((419321727/19531250000 : ℚ) : ℝ) ≤ stT308 150 := by
  have hc : ((8217/31250 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((419321727/19531250000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((8217/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c151 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((29487/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1854791/10000000) (δ := 973/62500000) (ψ := -270827/250000) 308 246
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t151 : ((5998227901/100000000000 : ℚ) : ℝ) ≤ stT308 151 := by
  have hc : ((29483/40000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5998227901/100000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((29483/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c152 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-93353/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 693733/1000000) (δ := 973/62500000) (ψ := -270827/250000) 308 246
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t152 : ((-18931869051/250000000000 : ℚ) : ℝ) ≤ stT308 152 := by
  have hc : ((-93363/100000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18931869051/250000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-93363/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c153 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((82129/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -930359/2500000) (δ := 1941/125000000) (ψ := -270827/250000) 308 247
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t153 : ((16579127277/2500000000000 : ℚ) : ℝ) ≤ stT308 153 := by
  have hc : ((82029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16579127277/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((82029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c154 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((434417/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1294883/10000000) (δ := 1941/125000000) (ψ := -270827/250000) 308 247
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t154 : ((175011242337/2500000000000 : ℚ) : ℝ) ≤ stT308 154 := by
  have hc : ((434367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175011242337/2500000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((434367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c155 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-807963/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1569677/2500000) (δ := 1941/125000000) (ψ := -270827/250000) 308 247
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t155 : ((-32452618143/500000000000 : ℚ) : ℝ) ≤ stT308 155 := by
  have hc : ((-808063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32452618143/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-808063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c156 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-109207/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2238731/5000000) (δ := 15421/1000000000) (ψ := -270827/250000) 308 248
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t156 : ((-87475633737/5000000000000 : ℚ) : ℝ) ≤ stT308 156 := by
  have hc : ((-109257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87475633737/5000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-109257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c157 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((984363/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 110671/2500000) (δ := 15421/1000000000) (ψ := -270827/250000) 308 248
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t157 : ((392763260309/5000000000000 : ℚ) : ℝ) ≤ stT308 157 := by
  have hc : ((984263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((392763260309/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((984263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c158 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-532737/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 333223/625000) (δ := 15421/1000000000) (ψ := -270827/250000) 308 248
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t158 : ((-211951369023/5000000000000 : ℚ) : ℝ) ≤ stT308 158 := by
  have hc : ((-532837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-211951369023/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-532837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c159 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-594407/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5518311/10000000) (δ := 15489/1000000000) (ψ := -270827/250000) 308 249
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t159 : ((-117868741341/2500000000000 : ℚ) : ℝ) ≤ stT308 159 := by
  have hc : ((-594507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117868741341/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-594507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c160 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((38483/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -690719/10000000) (δ := 15489/1000000000) (ψ := -270827/250000) 308 249
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t160 : ((30420304551/400000000000 : ℚ) : ℝ) ≤ stT308 160 := by
  have hc : ((38479/40000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30420304551/400000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((38479/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c161 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-8981/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2053383/5000000) (δ := 15489/1000000000) (ψ := -270827/250000) 308 249
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t161 : ((-14175752557/2500000000000 : ℚ) : ℝ) ≤ stT308 161 := by
  have hc : ((-17987/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14175752557/2500000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-17987/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c162 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-917817/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6833357/10000000) (δ := 3899/250000000) (ψ := -270827/250000) 308 250
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t162 : ((-28847377559/400000000000 : ℚ) : ℝ) ≤ stT308 162 := by
  have hc : ((-917917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28847377559/400000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-917917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c163 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((334497/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1047427/5000000) (δ := 3899/250000000) (ψ := -270827/250000) 308 250
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t163 : ((13097947861/250000000000 : ℚ) : ℝ) ≤ stT308 163 := by
  have hc : ((334447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13097947861/250000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((334447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c164 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((31323/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 130731/500000) (δ := 3899/250000000) (ψ := -270827/250000) 308 250
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t164 : ((24454247939/625000000000 : ℚ) : ℝ) ≤ stT308 164 := by
  have hc : ((125267/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24454247939/625000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((125267/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c165 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-975147/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 145909/200000) (δ := 3899/250000000) (ψ := -270827/250000) 308 250
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t165 : ((-759228814253/10000000000000 : ℚ) : ℝ) ≤ stT308 165 := by
  have hc : ((-975247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-759228814253/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-975247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c166 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((66769/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3759943/10000000) (δ := 15499/1000000000) (ψ := -270827/250000) 308 251
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t166 : ((1034902887/200000000000 : ℚ) : ℝ) ≤ stT308 166 := by
  have hc : ((66669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1034902887/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((66669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c167 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((94077/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 432377/5000000) (δ := 15499/1000000000) (ψ := -270827/250000) 308 251
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t167 : ((72791208141/1000000000000 : ℚ) : ℝ) ≤ stT308 167 := by
  have hc : ((94067/100000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72791208141/1000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((94067/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c168 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-576057/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5461731/10000000) (δ := 15499/1000000000) (ψ := -270827/250000) 308 251
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t168 : ((-444514920169/10000000000000 : ℚ) : ℝ) ≤ stT308 168 := by
  have hc : ((-576157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-444514920169/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-576157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c169 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-40253/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1419109/2500000) (δ := 15411/1000000000) (ψ := -270827/250000) 308 252
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t169 : ((-123874652547/2500000000000 : ℚ) : ℝ) ≤ stT308 169 := by
  have hc : ((-161037/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123874652547/2500000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-161037/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c170 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((449467/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1133667/10000000) (δ := 15411/1000000000) (ψ := -270827/250000) 308 252
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t170 : ((86171664997/1250000000000 : ℚ) : ℝ) ≤ stT308 170 := by
  have hc : ((449417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86171664997/1250000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((449417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c171 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((108047/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 169123/500000) (δ := 15411/1000000000) (ψ := -270827/250000) 308 252
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t171 : ((82587357843/5000000000000 : ℚ) : ℝ) ≤ stT308 171 := by
  have hc : ((107997/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82587357843/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((107997/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c172 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-999973/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -783571/1000000) (δ := 7759/500000000) (ψ := -270827/250000) 308 253
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t172 : ((-762548661989/10000000000000 : ℚ) : ℝ) ≤ stT308 172 := by
  have hc : ((-1000073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-762548661989/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-1000073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c173 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((1101/5000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3371943/10000000) (δ := 7759/500000000) (ψ := -270827/250000) 308 253
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t173 : ((334677457/20000000000 : ℚ) : ℝ) ≤ stT308 173 := by
  have hc : ((2201/10000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334677457/20000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((2201/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c174 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((910443/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 533053/5000000) (δ := 7759/500000000) (ψ := -270827/250000) 308 253
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t174 : ((345064603807/5000000000000 : ℚ) : ℝ) ≤ stT308 174 := by
  have hc : ((910343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((345064603807/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((910343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c175 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-290803/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1095749/2000000) (δ := 7759/500000000) (ψ := -270827/250000) 308 253
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t175 : ((-219864217437/5000000000000 : ℚ) : ℝ) ≤ stT308 175 := by
  have hc : ((-290853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219864217437/5000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-290853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c176 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-693191/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5841759/10000000) (δ := 7789/500000000) (ψ := -270827/250000) 308 254
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t176 : ((-522588196689/10000000000000 : ℚ) : ℝ) ≤ stT308 176 := by
  have hc : ((-693291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-522588196689/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-693291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c177 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((830029/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1479093/10000000) (δ := 7789/500000000) (ψ := -270827/250000) 308 254
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t177 : ((311906406567/5000000000000 : ℚ) : ℝ) ≤ stT308 177 := by
  have hc : ((829929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((311906406567/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((829929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c178 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((82869/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2858933/10000000) (δ := 7789/500000000) (ψ := -270827/250000) 308 254
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t178 : ((62097893819/2000000000000 : ℚ) : ℝ) ≤ stT308 178 := by
  have hc : ((82849/200000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62097893819/2000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((82849/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c179 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-481549/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 224147/312500) (δ := 7789/500000000) (ψ := -270827/250000) 308 254
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t179 : ((-89991107541/1250000000000 : ℚ) : ℝ) ≤ stT308 179 := by
  have hc : ((-481599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89991107541/1250000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-481599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c180 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-25419/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4245589/10000000) (δ := 15471/1000000000) (ψ := -270827/250000) 308 255
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t180 : ((-4740277821/500000000000 : ℚ) : ℝ) ≤ stT308 180 := by
  have hc : ((-25439/200000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4740277821/500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-25439/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c181 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((999967/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4073/2000000) (δ := 15471/1000000000) (ψ := -270827/250000) 308 255
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t181 : ((371597570949/5000000000000 : ℚ) : ℝ) ≤ stT308 181 := by
  have hc : ((999867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((371597570949/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((999867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c182 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-133903/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4262757/10000000) (δ := 15471/1000000000) (ψ := -270827/250000) 308 255
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t182 : ((-79463779/8000000000 : ℚ) : ℝ) ≤ stT308 182 := by
  have hc : ((-134003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79463779/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-134003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c183 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-121077/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7225991/10000000) (δ := 15439/1000000000) (ψ := -270827/250000) 308 256
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t183 : ((-89512022369/1250000000000 : ℚ) : ℝ) ≤ stT308 183 := by
  have hc : ((-242179/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89512022369/1250000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-242179/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c184 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((351223/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3029799/10000000) (δ := 15439/1000000000) (ψ := -270827/250000) 308 256
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t184 : ((258851035707/10000000000000 : ℚ) : ℝ) ≤ stT308 184 := by
  have hc : ((351123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258851035707/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((351123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c185 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((224293/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 571839/5000000) (δ := 15439/1000000000) (ψ := -270827/250000) 308 256
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t185 : ((20610621669/312500000000 : ℚ) : ℝ) ≤ stT308 185 := by
  have hc : ((56067/62500 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20610621669/312500000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((56067/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c186 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-520163/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2647297/5000000) (δ := 15439/1000000000) (ψ := -270827/250000) 308 256
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t186 : ((-95368890267/2500000000000 : ℚ) : ℝ) ≤ stT308 186 := by
  have hc : ((-520263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95368890267/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-520263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c187 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-202339/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6284629/10000000) (δ := 15547/1000000000) (ψ := -270827/250000) 308 257
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t187 : ((-36995832343/625000000000 : ℚ) : ℝ) ≤ stT308 187 := by
  have hc : ((-50591/62500 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36995832343/625000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-50591/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c188 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((643913/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -544497/2500000) (δ := 15547/1000000000) (ψ := -270827/250000) 308 257
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t188 : ((117387068103/2500000000000 : ℚ) : ℝ) ≤ stT308 188 := by
  have hc : ((643813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117387068103/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((643813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c189 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((722921/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1906939/10000000) (δ := 15547/1000000000) (ψ := -270827/250000) 308 257
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t189 : ((16430444151/312500000000 : ℚ) : ℝ) ≤ stT308 189 := by
  have hc : ((722821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16430444151/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((722821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c190 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-364649/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5970229/10000000) (δ := 15547/1000000000) (ψ := -270827/250000) 308 257
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t190 : ((-264580736423/5000000000000 : ℚ) : ℝ) ≤ stT308 190 := by
  have hc : ((-364699/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264580736423/5000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-364699/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c191 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-649923/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5695697/10000000) (δ := 15549/1000000000) (ψ := -270827/250000) 308 258
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t191 : ((-18813615689/400000000000 : ℚ) : ℝ) ≤ stT308 191 := by
  have hc : ((-650023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18813615689/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-650023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c192 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((783863/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -837417/5000000) (δ := 15549/1000000000) (ψ := -270827/250000) 308 258
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t192 : ((565631568181/10000000000000 : ℚ) : ℝ) ≤ stT308 192 := by
  have hc : ((783763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((565631568181/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((783763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c193 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((298891/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1162581/5000000) (δ := 15549/1000000000) (ψ := -270827/250000) 308 258
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t193 : ((43022046883/1000000000000 : ℚ) : ℝ) ≤ stT308 193 := by
  have hc : ((298841/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43022046883/1000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((298841/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c194 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-203501/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3152261/5000000) (δ := 15549/1000000000) (ψ := -270827/250000) 308 258
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t194 : ((-73061661717/1250000000000 : ℚ) : ℝ) ≤ stT308 194 := by
  have hc : ((-101763/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73061661717/1250000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-101763/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c195 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-57043/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5444563/10000000) (δ := 7721/500000000) (ψ := -270827/250000) 308 259
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t195 : ((-8171301819/200000000000 : ℚ) : ℝ) ≤ stT308 195 := by
  have hc : ((-57053/100000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8171301819/200000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-57053/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c196 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((823993/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -94121/625000) (δ := 7721/500000000) (ψ := -270827/250000) 308 259
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t196 : ((117698882301/2000000000000 : ℚ) : ℝ) ≤ stT308 196 := by
  have hc : ((823893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117698882301/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((823893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c197 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((569361/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2412671/10000000) (δ := 7721/500000000) (ψ := -270827/250000) 308 259
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t197 : ((40558138467/1000000000000 : ℚ) : ℝ) ≤ stT308 197 := by
  have hc : ((569261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40558138467/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((569261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c198 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-407801/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1577853/2500000) (δ := 7721/500000000) (ψ := -270827/250000) 308 259
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t198 : ((-28984747017/500000000000 : ℚ) : ℝ) ≤ stT308 198 := by
  have hc : ((-407851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28984747017/500000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-407851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c199 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-37133/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1103489/2000000) (δ := 3867/250000000) (ψ := -270827/250000) 308 260
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t199 : ((-52654691637/1250000000000 : ℚ) : ℝ) ≤ stT308 199 := by
  have hc : ((-148557/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52654691637/1250000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-148557/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c200 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((788071/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -82891/500000) (δ := 3867/250000000) (ψ := -270827/250000) 308 260
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t200 : ((278589510963/5000000000000 : ℚ) : ℝ) ≤ stT308 200 := by
  have hc : ((787971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((278589510963/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((787971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c201 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((64249/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 272829/1250000) (δ := 3867/250000000) (ψ := -270827/250000) 308 260
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t201 : ((9062131491/200000000000 : ℚ) : ℝ) ≤ stT308 201 := by
  have hc : ((64239/100000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9062131491/200000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((64239/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c202 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-14769/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6003911/10000000) (δ := 3867/250000000) (ψ := -270827/250000) 308 260
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t202 : ((-5196423029/100000000000 : ℚ) : ℝ) ≤ stT308 202 := by
  have hc : ((-14771/20000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5196423029/100000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-14771/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c203 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-88779/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5901561/10000000) (δ := 623/40000000) (ψ := -270827/250000) 308 261
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t203 : ((-124638937129/2500000000000 : ℚ) : ℝ) ≤ stT308 203 := by
  have hc : ((-177583/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124638937129/2500000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-177583/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c204 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((13243/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2117781/10000000) (δ := 623/40000000) (ψ := -270827/250000) 308 261
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t204 : ((463527687/10000000000 : ℚ) : ℝ) ≤ stT308 204 := by
  have hc : ((13241/20000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((463527687/10000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((13241/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c205 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((3953/5000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1647519/10000000) (δ := 623/40000000) (ψ := -270827/250000) 308 261
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t205 : ((110421783/2000000000 : ℚ) : ℝ) ≤ stT308 205 := by
  have hc : ((1581/2000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110421783/2000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((1581/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c206 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-276933/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5394493/10000000) (δ := 623/40000000) (ψ := -270827/250000) 308 261
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t206 : ((-96491736761/2500000000000 : ℚ) : ℝ) ≤ stT308 206 := by
  have hc : ((-276983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96491736761/2500000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-276983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c207 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-873853/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6584669/10000000) (δ := 97/6250000) (ψ := -270827/250000) 308 262
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t207 : ((-607440158697/10000000000000 : ℚ) : ℝ) ≤ stT308 207 := by
  have hc : ((-873953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-607440158697/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-873953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c208 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((408923/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -179613/625000) (δ := 97/6250000) (ψ := -270827/250000) 308 262
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t208 : ((2267741181/80000000000 : ℚ) : ℝ) ≤ stT308 208 := by
  have hc : ((408823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2267741181/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((408823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c209 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((946783/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 409633/5000000) (δ := 97/6250000) (ψ := -270827/250000) 308 262
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t209 : ((327416942331/5000000000000 : ℚ) : ℝ) ≤ stT308 209 := by
  have hc : ((946683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((327416942331/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((946683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c210 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-11257/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4494707/10000000) (δ := 97/6250000) (ψ := -270827/250000) 308 262
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t210 : ((-1942880823/125000000000 : ℚ) : ℝ) ≤ stT308 210 := by
  have hc : ((-5631/25000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1942880823/125000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-5631/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c211 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-992871/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3777647/5000000) (δ := 15413/1000000000) (ψ := -270827/250000) 308 263
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t211 : ((-683590032559/10000000000000 : ℚ) : ℝ) ≤ stT308 211 := by
  have hc : ((-992971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-683590032559/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-992971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c212 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((2467/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3914657/10000000) (δ := 15413/1000000000) (ψ := -270827/250000) 308 263
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t212 : ((830000217/2500000000000 : ℚ) : ℝ) ≤ stT308 212 := by
  have hc : ((2417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((830000217/2500000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((2417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c213 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((248307/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -145557/5000000) (δ := 15413/1000000000) (ψ := -270827/250000) 308 263
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t213 : ((21264980877/312500000000 : ℚ) : ℝ) ≤ stT308 213 := by
  have hc : ((124141/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21264980877/312500000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((124141/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c214 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((242169/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3315489/10000000) (δ := 15413/1000000000) (ψ := -270827/250000) 308 263
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t214 : ((33094947473/2000000000000 : ℚ) : ℝ) ≤ stT308 214 := by
  have hc : ((242069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33094947473/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((242069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c215 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-18577/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6905229/10000000) (δ := 15413/1000000000) (ψ := -270827/250000) 308 263
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t215 : ((-2534157021/40000000000 : ℚ) : ℝ) ≤ stT308 215 := by
  have hc : ((-18579/20000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2534157021/40000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-18579/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c216 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-99559/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2614813/5000000) (δ := 15497/1000000000) (ψ := -270827/250000) 308 264
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t216 : ((-33877472853/1000000000000 : ℚ) : ℝ) ≤ stT308 216 := by
  have hc : ((-99579/200000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33877472853/1000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-99579/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c217 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((7843/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1673073/10000000) (δ := 15497/1000000000) (ψ := -270827/250000) 308 264
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t217 : ((665436831/12500000000 : ℚ) : ℝ) ≤ stT308 217 := by
  have hc : ((3921/5000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((665436831/12500000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((3921/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c218 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((11466/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 466789/2500000) (δ := 15497/1000000000) (ψ := -270827/250000) 308 264
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t218 : ((24847012967/500000000000 : ℚ) : ℝ) ≤ stT308 218 := by
  have hc : ((183431/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24847012967/500000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((183431/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c219 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-276387/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1078243/2000000) (δ := 15497/1000000000) (ψ := -270827/250000) 308 264
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t219 : ((-93399492753/2500000000000 : ℚ) : ℝ) ≤ stT308 219 := by
  have hc : ((-276437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93399492753/2500000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-276437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c220 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-91387/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6808783/10000000) (δ := 15599/1000000000) (ψ := -270827/250000) 308 265
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t220 : ((-308099287/5000000000 : ℚ) : ℝ) ≤ stT308 220 := by
  have hc : ((-91397/100000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-308099287/5000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-91397/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c221 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((241707/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3316679/10000000) (δ := 15599/1000000000) (ψ := -270827/250000) 308 265
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t221 : ((5078820747/312500000000 : ℚ) : ℝ) ≤ stT308 221 := by
  have hc : ((241607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5078820747/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((241607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c222 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((249491/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 159563/10000000) (δ := 15599/1000000000) (ψ := -270827/250000) 308 265
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t222 : ((20928825337/312500000000 : ℚ) : ℝ) ≤ stT308 222 := by
  have hc : ((124733/125000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20928825337/312500000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((124733/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c223 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((30597/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3620251/10000000) (δ := 15599/1000000000) (ψ := -270827/250000) 308 265
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t223 : ((5118127307/625000000000 : ℚ) : ℝ) ≤ stT308 223 := by
  have hc : ((7643/62500 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5118127307/625000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((7643/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c224 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-95067/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3532731/5000000) (δ := 15599/1000000000) (ψ := -270827/250000) 308 265
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t224 : ((-31763038929/500000000000 : ℚ) : ℝ) ≤ stT308 224 := by
  have hc : ((-95077/100000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31763038929/500000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-95077/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c225 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-491881/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5212613/10000000) (δ := 3873/250000000) (ψ := -270827/250000) 308 266
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t225 : ((-327987497327/10000000000000 : ℚ) : ℝ) ≤ stT308 225 := by
  have hc : ((-491981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-327987497327/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-491981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c226 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((752331/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1798009/10000000) (δ := 30911/1000000000) (ψ := -270827/250000) 308 266
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t226 : ((50037653889/1000000000000 : ℚ) : ℝ) ≤ stT308 226 := by
  have hc : ((752231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50037653889/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((752231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c227 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((400859/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1601579/10000000) (δ := 3873/250000000) (ψ := -270827/250000) 308 266
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t227 : ((266026151907/5000000000000 : ℚ) : ℝ) ≤ stT308 227 := by
  have hc : ((400809/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((266026151907/5000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((400809/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c228 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-205559/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4986191/10000000) (δ := 3873/250000000) (ψ := -270827/250000) 308 266
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t228 : ((-136168055603/5000000000000 : ℚ) : ℝ) ≤ stT308 228 := by
  have hc : ((-205609/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136168055603/5000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-205609/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c229 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-15311/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -918993/1250000) (δ := 7709/500000000) (ψ := -270827/250000) 308 267
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t229 : ((-161901315819/2500000000000 : ℚ) : ℝ) ≤ stT308 229 := by
  have hc : ((-245001/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161901315819/2500000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-245001/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c230 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-27929/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3996823/10000000) (δ := 7709/500000000) (ψ := -270827/250000) 308 267
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t230 : ((-18481790049/10000000000000 : ℚ) : ℝ) ≤ stT308 230 := by
  have hc : ((-28029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18481790049/10000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-28029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c231 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((60359/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -131251/2000000) (δ := 7709/500000000) (ψ := -270827/250000) 308 267
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t231 : ((158836608861/2500000000000 : ℚ) : ℝ) ≤ stT308 231 := by
  have hc : ((241411/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158836608861/2500000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((241411/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c232 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((96387/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2669837/10000000) (δ := 7709/500000000) (ψ := -270827/250000) 308 267
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t232 : ((15817004811/500000000000 : ℚ) : ℝ) ≤ stT308 232 := by
  have hc : ((96367/200000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15817004811/500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((96367/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c233 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-29297/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1495421/2500000) (δ := 7709/500000000) (ψ := -270827/250000) 308 267
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t233 : ((-9597864861/200000000000 : ℚ) : ℝ) ≤ stT308 233 := by
  have hc : ((-29301/40000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9597864861/200000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-29301/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c234 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-841819/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32143/50000) (δ := 7763/500000000) (ψ := -270827/250000) 308 268
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t234 : ((-550380130599/10000000000000 : ℚ) : ℝ) ≤ stT308 234 := by
  have hc : ((-841919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-550380130599/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-841919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c235 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((76929/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -786253/2500000) (δ := 7763/500000000) (ψ := -270827/250000) 308 268
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t235 : ((783853633/39062500000 : ℚ) : ℝ) ≤ stT308 235 := by
  have hc : ((9613/31250 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((783853633/39062500000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((9613/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c236 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((998757/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 124639/10000000) (δ := 7763/500000000) (ψ := -270827/250000) 308 268
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t236 : ((10157340347/156250000000 : ℚ) : ℝ) ≤ stT308 236 := by
  have hc : ((998657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10157340347/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((998657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c237 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((216887/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 338043/1000000) (δ := 7763/500000000) (ψ := -270827/250000) 308 268
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t237 : ((140818114803/10000000000000 : ℚ) : ℝ) ≤ stT308 237 := by
  have hc : ((216787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140818114803/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((216787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c238 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-881113/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1324503/2000000) (δ := 7763/500000000) (ψ := -270827/250000) 308 268
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t238 : ((-142801447863/2500000000000 : ℚ) : ℝ) ≤ stT308 238 := by
  have hc : ((-881213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142801447863/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-881213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c239 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-174387/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1464229/2500000) (δ := 1557/100000000) (ψ := -270827/250000) 308 269
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t239 : ((-28204469741/625000000000 : ℚ) : ℝ) ≤ stT308 239 := by
  have hc : ((-43603/62500 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28204469741/625000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-43603/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c240 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((491711/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1320929/5000000) (δ := 1557/100000000) (ψ := -270827/250000) 308 269
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t240 : ((317333425667/10000000000000 : ℚ) : ℝ) ≤ stT308 240 := by
  have hc : ((491611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((317333425667/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((491611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c241 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((487517/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 279901/5000000) (δ := 1557/100000000) (ψ := -270827/250000) 308 269
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t241 : ((78501198213/1250000000000 : ℚ) : ℝ) ≤ stT308 241 := by
  have hc : ((487467/500000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78501198213/1250000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((487467/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c242 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((8931/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1874109/5000000) (δ := 1557/100000000) (ψ := -270827/250000) 308 269
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t242 : ((1433256461/312500000000 : ℚ) : ℝ) ≤ stT308 242 := by
  have hc : ((17837/250000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1433256461/312500000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((17837/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c243 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-931527/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6923467/10000000) (δ := 1557/100000000) (ψ := -270827/250000) 308 269
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t243 : ((-597639652127/10000000000000 : ℚ) : ℝ) ≤ stT308 243 := by
  have hc : ((-931627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-597639652127/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-931627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c244 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-15683/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -281113/500000) (δ := 15463/1000000000) (ψ := -270827/250000) 308 270
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t244 : ((-4016648727/100000000000 : ℚ) : ℝ) ≤ stT308 244 := by
  have hc : ((-31371/50000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4016648727/100000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-31371/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c245 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((549359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1236499/5000000) (δ := 1547/50000000) (ψ := -270827/250000) 308 270
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t245 : ((87727098221/2500000000000 : ℚ) : ℝ) ≤ stT308 245 := by
  have hc : ((549259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87727098221/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((549259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c246 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((96499/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 663481/10000000) (δ := 15463/1000000000) (ψ := -270827/250000) 308 270
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t246 : ((7689883833/125000000000 : ℚ) : ℝ) ≤ stT308 246 := by
  have hc : ((96489/100000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7689883833/125000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((96489/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c247 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((1397/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3787217/10000000) (δ := 15463/1000000000) (ψ := -270827/250000) 308 270
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t247 : ((443649019/125000000000 : ℚ) : ℝ) ≤ stT308 247 := by
  have hc : ((2789/50000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((443649019/125000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((2789/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c248 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-927823/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 275933/400000) (δ := 15463/1000000000) (ψ := -270827/250000) 308 270
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t248 : ((-589232032923/10000000000000 : ℚ) : ℝ) ≤ stT308 248 := by
  have hc : ((-927923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-589232032923/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-927923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c249 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-654587/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5711081/10000000) (δ := 15447/1000000000) (ψ := -270827/250000) 308 271
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t249 : ((-16595660763/400000000000 : ℚ) : ℝ) ≤ stT308 249 := by
  have hc : ((-654687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16595660763/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-654687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_c250 :
    |Real.cos (((308 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((3981/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -656211/2500000) (δ := 15447/1000000000) (ψ := -270827/250000) 308 271
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st308_t250 : ((2517297391/80000000000 : ℚ) : ℝ) ≤ stT308 250 := by
  have hc : ((19901/40000 : ℚ) : ℝ)
      ≤ Real.cos (((308 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st308_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2517297391/80000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((19901/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st308_p1 : ((117077/250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT308 (i+1) := by
  rw [Finset.sum_range_one]
  exact st308_t1

theorem st308_p2 : ((4414020240231/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT308 (i+1))
      = (∑ i ∈ Finset.range 1, stT308 (i+1)) + stT308 2 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 1
    simpa using h
  have hprev := st308_p1
  have hstep := st308_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p3 : ((56732880953/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT308 (i+1))
      = (∑ i ∈ Finset.range 2, stT308 (i+1)) + stT308 3 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 2
    simpa using h
  have hprev := st308_p2
  have hstep := st308_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p4 : ((281052383187/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT308 (i+1))
      = (∑ i ∈ Finset.range 3, stT308 (i+1)) + stT308 4 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 3
    simpa using h
  have hprev := st308_p3
  have hstep := st308_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p5 : ((2759123466091/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT308 (i+1))
      = (∑ i ∈ Finset.range 4, stT308 (i+1)) + stT308 5 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 4
    simpa using h
  have hprev := st308_p4
  have hstep := st308_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p6 : ((6538448977777/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT308 (i+1))
      = (∑ i ∈ Finset.range 5, stT308 (i+1)) + stT308 6 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 5
    simpa using h
  have hprev := st308_p5
  have hstep := st308_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p7 : ((22642607756523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT308 (i+1))
      = (∑ i ∈ Finset.range 6, stT308 (i+1)) + stT308 7 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 6
    simpa using h
  have hprev := st308_p6
  have hstep := st308_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p8 : ((25421359917873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT308 (i+1))
      = (∑ i ∈ Finset.range 7, stT308 (i+1)) + stT308 8 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 7
    simpa using h
  have hprev := st308_p7
  have hstep := st308_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p9 : ((1392367817097/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT308 (i+1))
      = (∑ i ∈ Finset.range 8, stT308 (i+1)) + stT308 9 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 8
    simpa using h
  have hprev := st308_p8
  have hstep := st308_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p10 : ((3860818108999/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT308 (i+1))
      = (∑ i ∈ Finset.range 9, stT308 (i+1)) + stT308 10 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 9
    simpa using h
  have hprev := st308_p9
  have hstep := st308_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p11 : ((3782205041677/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT308 (i+1))
      = (∑ i ∈ Finset.range 10, stT308 (i+1)) + stT308 11 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 10
    simpa using h
  have hprev := st308_p10
  have hstep := st308_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p12 : ((33125347437069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT308 (i+1))
      = (∑ i ∈ Finset.range 11, stT308 (i+1)) + stT308 12 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 11
    simpa using h
  have hprev := st308_p11
  have hstep := st308_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p13 : ((35424051972069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT308 (i+1))
      = (∑ i ∈ Finset.range 12, stT308 (i+1)) + stT308 13 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 12
    simpa using h
  have hprev := st308_p12
  have hstep := st308_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p14 : ((8207019037461/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT308 (i+1))
      = (∑ i ∈ Finset.range 13, stT308 (i+1)) + stT308 14 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 13
    simpa using h
  have hprev := st308_p13
  have hstep := st308_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p15 : ((8773165091251/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT308 (i+1))
      = (∑ i ∈ Finset.range 14, stT308 (i+1)) + stT308 15 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 14
    simpa using h
  have hprev := st308_p14
  have hstep := st308_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p16 : ((9313163841251/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT308 (i+1))
      = (∑ i ∈ Finset.range 15, stT308 (i+1)) + stT308 16 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 15
    simpa using h
  have hprev := st308_p15
  have hstep := st308_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p17 : ((617664195143/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT308 (i+1))
      = (∑ i ∈ Finset.range 16, stT308 (i+1)) + stT308 17 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 16
    simpa using h
  have hprev := st308_p16
  have hstep := st308_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p18 : ((1025138557121/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT308 (i+1))
      = (∑ i ∈ Finset.range 17, stT308 (i+1)) + stT308 18 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 17
    simpa using h
  have hprev := st308_p17
  have hstep := st308_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p19 : ((19357023901139/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT308 (i+1))
      = (∑ i ∈ Finset.range 18, stT308 (i+1)) + stT308 19 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 18
    simpa using h
  have hprev := st308_p18
  have hstep := st308_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p20 : ((20463912843211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT308 (i+1))
      = (∑ i ∈ Finset.range 19, stT308 (i+1)) + stT308 20 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 19
    simpa using h
  have hprev := st308_p19
  have hstep := st308_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p21 : ((39055911078821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT308 (i+1))
      = (∑ i ∈ Finset.range 20, stT308 (i+1)) + stT308 21 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 20
    simpa using h
  have hprev := st308_p20
  have hstep := st308_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p22 : ((7665332827689/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT308 (i+1))
      = (∑ i ∈ Finset.range 21, stT308 (i+1)) + stT308 22 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 21
    simpa using h
  have hprev := st308_p21
  have hstep := st308_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p23 : ((39786648604941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT308 (i+1))
      = (∑ i ∈ Finset.range 22, stT308 (i+1)) + stT308 23 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 22
    simpa using h
  have hprev := st308_p22
  have hstep := st308_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p24 : ((41762696449883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT308 (i+1))
      = (∑ i ∈ Finset.range 23, stT308 (i+1)) + stT308 24 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 23
    simpa using h
  have hprev := st308_p23
  have hstep := st308_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p25 : ((43702182449883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT308 (i+1))
      = (∑ i ∈ Finset.range 24, stT308 (i+1)) + stT308 25 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 24
    simpa using h
  have hprev := st308_p24
  have hstep := st308_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p26 : ((45159984022979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT308 (i+1))
      = (∑ i ∈ Finset.range 25, stT308 (i+1)) + stT308 26 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 25
    simpa using h
  have hprev := st308_p25
  have hstep := st308_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p27 : ((22479843866201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT308 (i+1))
      = (∑ i ∈ Finset.range 26, stT308 (i+1)) + stT308 27 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 26
    simpa using h
  have hprev := st308_p26
  have hstep := st308_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p28 : ((21539702279453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT308 (i+1))
      = (∑ i ∈ Finset.range 27, stT308 (i+1)) + stT308 28 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 27
    simpa using h
  have hprev := st308_p27
  have hstep := st308_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p29 : ((43238614138267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT308 (i+1))
      = (∑ i ∈ Finset.range 28, stT308 (i+1)) + stT308 29 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 28
    simpa using h
  have hprev := st308_p28
  have hstep := st308_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p30 : ((4470300995677/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT308 (i+1))
      = (∑ i ∈ Finset.range 29, stT308 (i+1)) + stT308 30 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 29
    simpa using h
  have hprev := st308_p29
  have hstep := st308_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p31 : ((4290785398377/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT308 (i+1))
      = (∑ i ∈ Finset.range 30, stT308 (i+1)) + stT308 31 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 30
    simpa using h
  have hprev := st308_p30
  have hstep := st308_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p32 : ((22271859945723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT308 (i+1))
      = (∑ i ∈ Finset.range 31, stT308 (i+1)) + stT308 32 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 31
    simpa using h
  have hprev := st308_p31
  have hstep := st308_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p33 : ((42969578769771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT308 (i+1))
      = (∑ i ∈ Finset.range 32, stT308 (i+1)) + stT308 33 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 32
    simpa using h
  have hprev := st308_p32
  have hstep := st308_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p34 : ((22323124644943/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT308 (i+1))
      = (∑ i ∈ Finset.range 33, stT308 (i+1)) + stT308 34 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 33
    simpa using h
  have hprev := st308_p33
  have hstep := st308_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p35 : ((8604822428433/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT308 (i+1))
      = (∑ i ∈ Finset.range 34, stT308 (i+1)) + stT308 35 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 34
    simpa using h
  have hprev := st308_p34
  have hstep := st308_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p36 : ((43877013467671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT308 (i+1))
      = (∑ i ∈ Finset.range 35, stT308 (i+1)) + stT308 36 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 35
    simpa using h
  have hprev := st308_p35
  have hstep := st308_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p37 : ((44589794490423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT308 (i+1))
      = (∑ i ∈ Finset.range 36, stT308 (i+1)) + stT308 37 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 36
    simpa using h
  have hprev := st308_p36
  have hstep := st308_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p38 : ((42973799062733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT308 (i+1))
      = (∑ i ∈ Finset.range 37, stT308 (i+1)) + stT308 38 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 37
    simpa using h
  have hprev := st308_p37
  have hstep := st308_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p39 : ((21533020427369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT308 (i+1))
      = (∑ i ∈ Finset.range 38, stT308 (i+1)) + stT308 39 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 38
    simpa using h
  have hprev := st308_p38
  have hstep := st308_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p40 : ((223235095799/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT308 (i+1))
      = (∑ i ∈ Finset.range 39, stT308 (i+1)) + stT308 40 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 39
    simpa using h
  have hprev := st308_p39
  have hstep := st308_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p41 : ((22514367896933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT308 (i+1))
      = (∑ i ∈ Finset.range 40, stT308 (i+1)) + stT308 41 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 40
    simpa using h
  have hprev := st308_p40
  have hstep := st308_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p42 : ((21913868441221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT308 (i+1))
      = (∑ i ∈ Finset.range 41, stT308 (i+1)) + stT308 42 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 41
    simpa using h
  have hprev := st308_p41
  have hstep := st308_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p43 : ((2118211382153/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT308 (i+1))
      = (∑ i ∈ Finset.range 42, stT308 (i+1)) + stT308 43 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 42
    simpa using h
  have hprev := st308_p42
  have hstep := st308_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p44 : ((41657308537291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT308 (i+1))
      = (∑ i ∈ Finset.range 43, stT308 (i+1)) + stT308 44 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 43
    simpa using h
  have hprev := st308_p43
  have hstep := st308_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p45 : ((209403226843/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT308 (i+1))
      = (∑ i ∈ Finset.range 44, stT308 (i+1)) + stT308 45 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 44
    simpa using h
  have hprev := st308_p44
  have hstep := st308_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p46 : ((5344653593479/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT308 (i+1))
      = (∑ i ∈ Finset.range 45, stT308 (i+1)) + stT308 46 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 45
    simpa using h
  have hprev := st308_p45
  have hstep := st308_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p47 : ((21983249181449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT308 (i+1))
      = (∑ i ∈ Finset.range 46, stT308 (i+1)) + stT308 47 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 46
    simpa using h
  have hprev := st308_p46
  have hstep := st308_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p48 : ((22650128845949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT308 (i+1))
      = (∑ i ∈ Finset.range 47, stT308 (i+1)) + stT308 48 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 47
    simpa using h
  have hprev := st308_p47
  have hstep := st308_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p49 : ((9330830600003/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT308 (i+1))
      = (∑ i ∈ Finset.range 48, stT308 (i+1)) + stT308 49 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 48
    simpa using h
  have hprev := st308_p48
  have hstep := st308_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p50 : ((47964610849057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT308 (i+1))
      = (∑ i ∈ Finset.range 49, stT308 (i+1)) + stT308 50 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 49
    simpa using h
  have hprev := st308_p49
  have hstep := st308_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p51 : ((49144005080737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT308 (i+1))
      = (∑ i ∈ Finset.range 50, stT308 (i+1)) + stT308 51 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 50
    simpa using h
  have hprev := st308_p50
  have hstep := st308_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p52 : ((50036418921487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT308 (i+1))
      = (∑ i ∈ Finset.range 51, stT308 (i+1)) + stT308 52 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 51
    simpa using h
  have hprev := st308_p51
  have hstep := st308_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p53 : ((50419698671847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT308 (i+1))
      = (∑ i ∈ Finset.range 52, stT308 (i+1)) + stT308 53 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 52
    simpa using h
  have hprev := st308_p52
  have hstep := st308_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p54 : ((50091956856327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT308 (i+1))
      = (∑ i ∈ Finset.range 53, stT308 (i+1)) + stT308 54 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 53
    simpa using h
  have hprev := st308_p53
  have hstep := st308_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p55 : ((49057047720727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT308 (i+1))
      = (∑ i ∈ Finset.range 54, stT308 (i+1)) + stT308 55 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 54
    simpa using h
  have hprev := st308_p54
  have hstep := st308_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p56 : ((47721545177541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT308 (i+1))
      = (∑ i ∈ Finset.range 55, stT308 (i+1)) + stT308 56 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 55
    simpa using h
  have hprev := st308_p55
  have hstep := st308_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p57 : ((5858312440257/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT308 (i+1))
      = (∑ i ∈ Finset.range 56, stT308 (i+1)) + stT308 57 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 56
    simpa using h
  have hprev := st308_p56
  have hstep := st308_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p58 : ((5894899983819/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT308 (i+1))
      = (∑ i ∈ Finset.range 57, stT308 (i+1)) + stT308 58 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 57
    simpa using h
  have hprev := st308_p57
  have hstep := st308_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p59 : ((48391644809403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT308 (i+1))
      = (∑ i ∈ Finset.range 58, stT308 (i+1)) + stT308 59 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 58
    simpa using h
  have hprev := st308_p58
  have hstep := st308_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p60 : ((49310374234533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT308 (i+1))
      = (∑ i ∈ Finset.range 59, stT308 (i+1)) + stT308 60 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 59
    simpa using h
  have hprev := st308_p59
  have hstep := st308_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p61 : ((48811432360399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT308 (i+1))
      = (∑ i ∈ Finset.range 60, stT308 (i+1)) + stT308 61 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 60
    simpa using h
  have hprev := st308_p60
  have hstep := st308_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p62 : ((1901928385243/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT308 (i+1))
      = (∑ i ∈ Finset.range 61, stT308 (i+1)) + stT308 62 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 61
    simpa using h
  have hprev := st308_p61
  have hstep := st308_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p63 : ((47408026340581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT308 (i+1))
      = (∑ i ∈ Finset.range 62, stT308 (i+1)) + stT308 63 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 62
    simpa using h
  have hprev := st308_p62
  have hstep := st308_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p64 : ((48619201340581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT308 (i+1))
      = (∑ i ∈ Finset.range 63, stT308 (i+1)) + stT308 64 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 63
    simpa using h
  have hprev := st308_p63
  have hstep := st308_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p65 : ((1531258652201/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT308 (i+1))
      = (∑ i ∈ Finset.range 64, stT308 (i+1)) + stT308 65 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 64
    simpa using h
  have hprev := st308_p64
  have hstep := st308_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p66 : ((47825089085227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT308 (i+1))
      = (∑ i ∈ Finset.range 65, stT308 (i+1)) + stT308 66 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 65
    simpa using h
  have hprev := st308_p65
  have hstep := st308_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p67 : ((23778180693971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT308 (i+1))
      = (∑ i ∈ Finset.range 66, stT308 (i+1)) + stT308 67 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 66
    simpa using h
  have hprev := st308_p66
  have hstep := st308_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p68 : ((12191436741793/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT308 (i+1))
      = (∑ i ∈ Finset.range 67, stT308 (i+1)) + stT308 68 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 67
    simpa using h
  have hprev := st308_p67
  have hstep := st308_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p69 : ((48593319446461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT308 (i+1))
      = (∑ i ∈ Finset.range 68, stT308 (i+1)) + stT308 69 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 68
    simpa using h
  have hprev := st308_p68
  have hstep := st308_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p70 : ((23751975341881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT308 (i+1))
      = (∑ i ∈ Finset.range 69, stT308 (i+1)) + stT308 70 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 69
    simpa using h
  have hprev := st308_p69
  have hstep := st308_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p71 : ((48328135671613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT308 (i+1))
      = (∑ i ∈ Finset.range 70, stT308 (i+1)) + stT308 71 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 70
    simpa using h
  have hprev := st308_p70
  have hstep := st308_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p72 : ((24392587600517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT308 (i+1))
      = (∑ i ∈ Finset.range 71, stT308 (i+1)) + stT308 72 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 71
    simpa using h
  have hprev := st308_p71
  have hstep := st308_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p73 : ((23808585369259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT308 (i+1))
      = (∑ i ∈ Finset.range 72, stT308 (i+1)) + stT308 73 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 72
    simpa using h
  have hprev := st308_p72
  have hstep := st308_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p74 : ((24130722581047/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT308 (i+1))
      = (∑ i ∈ Finset.range 73, stT308 (i+1)) + stT308 74 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 73
    simpa using h
  have hprev := st308_p73
  have hstep := st308_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p75 : ((24358241782297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT308 (i+1))
      = (∑ i ∈ Finset.range 74, stT308 (i+1)) + stT308 75 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 74
    simpa using h
  have hprev := st308_p74
  have hstep := st308_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p76 : ((47598897112763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT308 (i+1))
      = (∑ i ∈ Finset.range 75, stT308 (i+1)) + stT308 76 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 75
    simpa using h
  have hprev := st308_p75
  have hstep := st308_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p77 : ((24250606210029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT308 (i+1))
      = (∑ i ∈ Finset.range 76, stT308 (i+1)) + stT308 77 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 76
    simpa using h
  have hprev := st308_p76
  have hstep := st308_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p78 : ((968184613689/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT308 (i+1))
      = (∑ i ∈ Finset.range 77, stT308 (i+1)) + stT308 78 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 77
    simpa using h
  have hprev := st308_p77
  have hstep := st308_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p79 : ((953672666121/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT308 (i+1))
      = (∑ i ∈ Finset.range 78, stT308 (i+1)) + stT308 79 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 78
    simpa using h
  have hprev := st308_p78
  have hstep := st308_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p80 : ((6098878667511/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT308 (i+1))
      = (∑ i ∈ Finset.range 79, stT308 (i+1)) + stT308 80 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 79
    simpa using h
  have hprev := st308_p79
  have hstep := st308_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p81 : ((5980256628169/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT308 (i+1))
      = (∑ i ∈ Finset.range 80, stT308 (i+1)) + stT308 81 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 80
    simpa using h
  have hprev := st308_p80
  have hstep := st308_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p82 : ((12064421567633/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT308 (i+1))
      = (∑ i ∈ Finset.range 81, stT308 (i+1)) + stT308 82 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 81
    simpa using h
  have hprev := st308_p81
  have hstep := st308_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p83 : ((24240946959189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT308 (i+1))
      = (∑ i ∈ Finset.range 82, stT308 (i+1)) + stT308 83 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 82
    simpa using h
  have hprev := st308_p82
  have hstep := st308_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p84 : ((11933941005967/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT308 (i+1))
      = (∑ i ∈ Finset.range 83, stT308 (i+1)) + stT308 84 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 83
    simpa using h
  have hprev := st308_p83
  have hstep := st308_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p85 : ((12191776344517/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT308 (i+1))
      = (∑ i ∈ Finset.range 84, stT308 (i+1)) + stT308 85 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 84
    simpa using h
  have hprev := st308_p84
  have hstep := st308_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p86 : ((2385009250499/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT308 (i+1))
      = (∑ i ∈ Finset.range 85, stT308 (i+1)) + stT308 86 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 85
    simpa using h
  have hprev := st308_p85
  have hstep := st308_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p87 : ((2430266046327/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT308 (i+1))
      = (∑ i ∈ Finset.range 86, stT308 (i+1)) + stT308 87 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 86
    simpa using h
  have hprev := st308_p86
  have hstep := st308_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p88 : ((11994961302887/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT308 (i+1))
      = (∑ i ∈ Finset.range 87, stT308 (i+1)) + stT308 88 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 87
    simpa using h
  have hprev := st308_p87
  have hstep := st308_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p89 : ((12070269849749/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT308 (i+1))
      = (∑ i ∈ Finset.range 88, stT308 (i+1)) + stT308 89 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 88
    simpa using h
  have hprev := st308_p88
  have hstep := st308_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p90 : ((6036640036489/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT308 (i+1))
      = (∑ i ∈ Finset.range 89, stT308 (i+1)) + stT308 90 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 89
    simpa using h
  have hprev := st308_p89
  have hstep := st308_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p91 : ((12002521883763/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT308 (i+1))
      = (∑ i ∈ Finset.range 90, stT308 (i+1)) + stT308 91 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 90
    simpa using h
  have hprev := st308_p90
  have hstep := st308_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p92 : ((12126960149967/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT308 (i+1))
      = (∑ i ∈ Finset.range 91, stT308 (i+1)) + stT308 92 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 91
    simpa using h
  have hprev := st308_p91
  have hstep := st308_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p93 : ((11962719915067/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT308 (i+1))
      = (∑ i ∈ Finset.range 92, stT308 (i+1)) + stT308 93 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 92
    simpa using h
  have hprev := st308_p92
  have hstep := st308_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p94 : ((12154456953283/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT308 (i+1))
      = (∑ i ∈ Finset.range 93, stT308 (i+1)) + stT308 94 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 93
    simpa using h
  have hprev := st308_p93
  have hstep := st308_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p95 : ((2986216208317/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT308 (i+1))
      = (∑ i ∈ Finset.range 94, stT308 (i+1)) + stT308 95 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 94
    simpa using h
  have hprev := st308_p94
  have hstep := st308_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p96 : ((3041215889187/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT308 (i+1))
      = (∑ i ∈ Finset.range 95, stT308 (i+1)) + stT308 96 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 95
    simpa using h
  have hprev := st308_p95
  have hstep := st308_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p97 : ((47759130811887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT308 (i+1))
      = (∑ i ∈ Finset.range 96, stT308 (i+1)) + stT308 97 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 96
    simpa using h
  have hprev := st308_p96
  have hstep := st308_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p98 : ((48662644095703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT308 (i+1))
      = (∑ i ∈ Finset.range 97, stT308 (i+1)) + stT308 98 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 97
    simpa using h
  have hprev := st308_p97
  have hstep := st308_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p99 : ((47770183417197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT308 (i+1))
      = (∑ i ∈ Finset.range 98, stT308 (i+1)) + stT308 99 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 98
    simpa using h
  have hprev := st308_p98
  have hstep := st308_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p100 : ((9727164910311/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT308 (i+1))
      = (∑ i ∈ Finset.range 99, stT308 (i+1)) + stT308 100 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 99
    simpa using h
  have hprev := st308_p99
  have hstep := st308_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p101 : ((47815066462217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT308 (i+1))
      = (∑ i ∈ Finset.range 100, stT308 (i+1)) + stT308 101 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 100
    simpa using h
  have hprev := st308_p100
  have hstep := st308_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p102 : ((24283535118403/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT308 (i+1))
      = (∑ i ∈ Finset.range 101, stT308 (i+1)) + stT308 102 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 101
    simpa using h
  have hprev := st308_p101
  have hstep := st308_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p103 : ((23956427235663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT308 (i+1))
      = (∑ i ∈ Finset.range 102, stT308 (i+1)) + stT308 103 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 102
    simpa using h
  have hprev := st308_p102
  have hstep := st308_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p104 : ((24216911448603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT308 (i+1))
      = (∑ i ∈ Finset.range 103, stT308 (i+1)) + stT308 104 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 103
    simpa using h
  have hprev := st308_p103
  have hstep := st308_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p105 : ((48084422038077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT308 (i+1))
      = (∑ i ∈ Finset.range 104, stT308 (i+1)) + stT308 105 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 104
    simpa using h
  have hprev := st308_p104
  have hstep := st308_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p106 : ((48223607178577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT308 (i+1))
      = (∑ i ∈ Finset.range 105, stT308 (i+1)) + stT308 106 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 105
    simpa using h
  have hprev := st308_p105
  have hstep := st308_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p107 : ((48325445082289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT308 (i+1))
      = (∑ i ∈ Finset.range 106, stT308 (i+1)) + stT308 107 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 106
    simpa using h
  have hprev := st308_p106
  have hstep := st308_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p108 : ((47966562024827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT308 (i+1))
      = (∑ i ∈ Finset.range 107, stT308 (i+1)) + stT308 108 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 107
    simpa using h
  have hprev := st308_p107
  have hstep := st308_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p109 : ((48572435818953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT308 (i+1))
      = (∑ i ∈ Finset.range 108, stT308 (i+1)) + stT308 109 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 108
    simpa using h
  have hprev := st308_p108
  have hstep := st308_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p110 : ((47763020102067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT308 (i+1))
      = (∑ i ∈ Finset.range 109, stT308 (i+1)) + stT308 110 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 109
    simpa using h
  have hprev := st308_p109
  have hstep := st308_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p111 : ((24346313657669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT308 (i+1))
      = (∑ i ∈ Finset.range 110, stT308 (i+1)) + stT308 111 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 110
    simpa using h
  have hprev := st308_p110
  have hstep := st308_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p112 : ((955245830557/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT308 (i+1))
      = (∑ i ∈ Finset.range 111, stT308 (i+1)) + stT308 112 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 111
    simpa using h
  have hprev := st308_p111
  have hstep := st308_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p113 : ((4854895827993/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT308 (i+1))
      = (∑ i ∈ Finset.range 112, stT308 (i+1)) + stT308 113 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 112
    simpa using h
  have hprev := st308_p112
  have hstep := st308_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p114 : ((24024633585433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT308 (i+1))
      = (∑ i ∈ Finset.range 113, stT308 (i+1)) + stT308 114 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 113
    simpa using h
  have hprev := st308_p113
  have hstep := st308_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p115 : ((24076248614337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT308 (i+1))
      = (∑ i ∈ Finset.range 114, stT308 (i+1)) + stT308 115 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 114
    simpa using h
  have hprev := st308_p114
  have hstep := st308_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p116 : ((24241433779497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT308 (i+1))
      = (∑ i ∈ Finset.range 115, stT308 (i+1)) + stT308 116 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 115
    simpa using h
  have hprev := st308_p115
  have hstep := st308_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p117 : ((11945284042239/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT308 (i+1))
      = (∑ i ∈ Finset.range 116, stT308 (i+1)) + stT308 117 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 116
    simpa using h
  have hprev := st308_p116
  have hstep := st308_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p118 : ((24342628374927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT308 (i+1))
      = (∑ i ∈ Finset.range 117, stT308 (i+1)) + stT308 118 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 117
    simpa using h
  have hprev := st308_p117
  have hstep := st308_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p119 : ((23912593873639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT308 (i+1))
      = (∑ i ∈ Finset.range 118, stT308 (i+1)) + stT308 119 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 118
    simpa using h
  have hprev := st308_p118
  have hstep := st308_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p120 : ((12094935644807/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT308 (i+1))
      = (∑ i ∈ Finset.range 119, stT308 (i+1)) + stT308 120 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 119
    simpa using h
  have hprev := st308_p119
  have hstep := st308_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p121 : ((9663675241891/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT308 (i+1))
      = (∑ i ∈ Finset.range 120, stT308 (i+1)) + stT308 121 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 120
    simpa using h
  have hprev := st308_p120
  have hstep := st308_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p122 : ((47853473065739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT308 (i+1))
      = (∑ i ∈ Finset.range 121, stT308 (i+1)) + stT308 122 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 121
    simpa using h
  have hprev := st308_p121
  have hstep := st308_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p123 : ((48682337704003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT308 (i+1))
      = (∑ i ∈ Finset.range 122, stT308 (i+1)) + stT308 123 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 122
    simpa using h
  have hprev := st308_p122
  have hstep := st308_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p124 : ((47810669592507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT308 (i+1))
      = (∑ i ∈ Finset.range 123, stT308 (i+1)) + stT308 124 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 123
    simpa using h
  have hprev := st308_p123
  have hstep := st308_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p125 : ((48358842434559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT308 (i+1))
      = (∑ i ∈ Finset.range 124, stT308 (i+1)) + stT308 125 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 124
    simpa using h
  have hprev := st308_p124
  have hstep := st308_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p126 : ((48383307506499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT308 (i+1))
      = (∑ i ∈ Finset.range 125, stT308 (i+1)) + stT308 126 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 125
    simpa using h
  have hprev := st308_p125
  have hstep := st308_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p127 : ((1911542897987/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT308 (i+1))
      = (∑ i ∈ Finset.range 126, stT308 (i+1)) + stT308 127 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 126
    simpa using h
  have hprev := st308_p126
  have hstep := st308_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p128 : ((6083371811399/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT308 (i+1))
      = (∑ i ∈ Finset.range 127, stT308 (i+1)) + stT308 128 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 127
    simpa using h
  have hprev := st308_p127
  have hstep := st308_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p129 : ((23978809006109/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT308 (i+1))
      = (∑ i ∈ Finset.range 128, stT308 (i+1)) + stT308 129 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 128
    simpa using h
  have hprev := st308_p128
  have hstep := st308_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p130 : ((24054436840391/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT308 (i+1))
      = (∑ i ∈ Finset.range 129, stT308 (i+1)) + stT308 130 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 129
    simpa using h
  have hprev := st308_p129
  have hstep := st308_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p131 : ((24303932191483/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT308 (i+1))
      = (∑ i ∈ Finset.range 130, stT308 (i+1)) + stT308 131 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 130
    simpa using h
  have hprev := st308_p130
  have hstep := st308_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p132 : ((47748986277491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT308 (i+1))
      = (∑ i ∈ Finset.range 131, stT308 (i+1)) + stT308 132 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 131
    simpa using h
  have hprev := st308_p131
  have hstep := st308_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p133 : ((24218641330419/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT308 (i+1))
      = (∑ i ∈ Finset.range 132, stT308 (i+1)) + stT308 133 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 132
    simpa using h
  have hprev := st308_p132
  have hstep := st308_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p134 : ((120914597417/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT308 (i+1))
      = (∑ i ∈ Finset.range 133, stT308 (i+1)) + stT308 134 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 133
    simpa using h
  have hprev := st308_p133
  have hstep := st308_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p135 : ((11941818847879/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT308 (i+1))
      = (∑ i ∈ Finset.range 134, stT308 (i+1)) + stT308 135 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 134
    simpa using h
  have hprev := st308_p134
  have hstep := st308_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p136 : ((6077847144073/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT308 (i+1))
      = (∑ i ∈ Finset.range 135, stT308 (i+1)) + stT308 136 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 135
    simpa using h
  have hprev := st308_p135
  have hstep := st308_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p137 : ((24063492757981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT308 (i+1))
      = (∑ i ∈ Finset.range 136, stT308 (i+1)) + stT308 137 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 136
    simpa using h
  have hprev := st308_p136
  have hstep := st308_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p138 : ((47889511201929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT308 (i+1))
      = (∑ i ∈ Finset.range 137, stT308 (i+1)) + stT308 138 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 137
    simpa using h
  have hprev := st308_p137
  have hstep := st308_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p139 : ((48680080094713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT308 (i+1))
      = (∑ i ∈ Finset.range 138, stT308 (i+1)) + stT308 139 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 138
    simpa using h
  have hprev := st308_p138
  have hstep := st308_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p140 : ((47965398433303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT308 (i+1))
      = (∑ i ∈ Finset.range 139, stT308 (i+1)) + stT308 140 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 139
    simpa using h
  have hprev := st308_p139
  have hstep := st308_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p141 : ((48014222979679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT308 (i+1))
      = (∑ i ∈ Finset.range 140, stT308 (i+1)) + stT308 141 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 140
    simpa using h
  have hprev := st308_p140
  have hstep := st308_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p142 : ((48675017596147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT308 (i+1))
      = (∑ i ∈ Finset.range 141, stT308 (i+1)) + stT308 142 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 141
    simpa using h
  have hprev := st308_p141
  have hstep := st308_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p143 : ((47880138519899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT308 (i+1))
      = (∑ i ∈ Finset.range 142, stT308 (i+1)) + stT308 143 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 142
    simpa using h
  have hprev := st308_p142
  have hstep := st308_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p144 : ((1923751270711/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT308 (i+1))
      = (∑ i ∈ Finset.range 143, stT308 (i+1)) + stT308 144 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 143
    simpa using h
  have hprev := st308_p143
  have hstep := st308_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p145 : ((48660198731653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT308 (i+1))
      = (∑ i ∈ Finset.range 144, stT308 (i+1)) + stT308 145 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 144
    simpa using h
  have hprev := st308_p144
  have hstep := st308_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p146 : ((47849780453061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT308 (i+1))
      = (∑ i ∈ Finset.range 145, stT308 (i+1)) + stT308 146 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 145
    simpa using h
  have hprev := st308_p145
  have hstep := st308_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p147 : ((48114567276143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT308 (i+1))
      = (∑ i ∈ Finset.range 146, stT308 (i+1)) + stT308 147 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 146
    simpa using h
  have hprev := st308_p146
  have hstep := st308_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p148 : ((48660510209129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT308 (i+1))
      = (∑ i ∈ Finset.range 147, stT308 (i+1)) + stT308 148 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 147
    simpa using h
  have hprev := st308_p147
  have hstep := st308_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p149 : ((9572303958677/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT308 (i+1))
      = (∑ i ∈ Finset.range 148, stT308 (i+1)) + stT308 149 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 148
    simpa using h
  have hprev := st308_p148
  have hstep := st308_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p150 : ((48076212517609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT308 (i+1))
      = (∑ i ∈ Finset.range 149, stT308 (i+1)) + stT308 150 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 149
    simpa using h
  have hprev := st308_p149
  have hstep := st308_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p151 : ((48676035307709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT308 (i+1))
      = (∑ i ∈ Finset.range 150, stT308 (i+1)) + stT308 151 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 150
    simpa using h
  have hprev := st308_p150
  have hstep := st308_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p152 : ((47918760545669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT308 (i+1))
      = (∑ i ∈ Finset.range 151, stT308 (i+1)) + stT308 152 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 151
    simpa using h
  have hprev := st308_p151
  have hstep := st308_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p153 : ((47985077054777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT308 (i+1))
      = (∑ i ∈ Finset.range 152, stT308 (i+1)) + stT308 153 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 152
    simpa using h
  have hprev := st308_p152
  have hstep := st308_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p154 : ((389480976193/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT308 (i+1))
      = (∑ i ∈ Finset.range 153, stT308 (i+1)) + stT308 154 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 153
    simpa using h
  have hprev := st308_p153
  have hstep := st308_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p155 : ((9607213932253/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT308 (i+1))
      = (∑ i ∈ Finset.range 154, stT308 (i+1)) + stT308 155 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 154
    simpa using h
  have hprev := st308_p154
  have hstep := st308_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p156 : ((47861118393791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT308 (i+1))
      = (∑ i ∈ Finset.range 155, stT308 (i+1)) + stT308 156 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 155
    simpa using h
  have hprev := st308_p155
  have hstep := st308_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p157 : ((48646644914409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT308 (i+1))
      = (∑ i ∈ Finset.range 156, stT308 (i+1)) + stT308 157 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 156
    simpa using h
  have hprev := st308_p156
  have hstep := st308_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p158 : ((48222742176363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT308 (i+1))
      = (∑ i ∈ Finset.range 157, stT308 (i+1)) + stT308 158 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 157
    simpa using h
  have hprev := st308_p157
  have hstep := st308_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p159 : ((47751267210999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT308 (i+1))
      = (∑ i ∈ Finset.range 158, stT308 (i+1)) + stT308 159 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 158
    simpa using h
  have hprev := st308_p158
  have hstep := st308_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p160 : ((24255887412387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT308 (i+1))
      = (∑ i ∈ Finset.range 159, stT308 (i+1)) + stT308 160 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 159
    simpa using h
  have hprev := st308_p159
  have hstep := st308_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p161 : ((24227535907273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT308 (i+1))
      = (∑ i ∈ Finset.range 160, stT308 (i+1)) + stT308 161 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 160
    simpa using h
  have hprev := st308_p160
  have hstep := st308_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p162 : ((47733887375571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT308 (i+1))
      = (∑ i ∈ Finset.range 161, stT308 (i+1)) + stT308 162 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 161
    simpa using h
  have hprev := st308_p161
  have hstep := st308_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p163 : ((48257805290011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT308 (i+1))
      = (∑ i ∈ Finset.range 162, stT308 (i+1)) + stT308 163 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 162
    simpa using h
  have hprev := st308_p162
  have hstep := st308_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p164 : ((9729814651407/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT308 (i+1))
      = (∑ i ∈ Finset.range 163, stT308 (i+1)) + stT308 164 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 163
    simpa using h
  have hprev := st308_p163
  have hstep := st308_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p165 : ((23944922221391/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT308 (i+1))
      = (∑ i ∈ Finset.range 164, stT308 (i+1)) + stT308 165 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 164
    simpa using h
  have hprev := st308_p164
  have hstep := st308_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p166 : ((11985397396783/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT308 (i+1))
      = (∑ i ∈ Finset.range 165, stT308 (i+1)) + stT308 166 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 165
    simpa using h
  have hprev := st308_p165
  have hstep := st308_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p167 : ((24334750834271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT308 (i+1))
      = (∑ i ∈ Finset.range 166, stT308 (i+1)) + stT308 167 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 166
    simpa using h
  have hprev := st308_p166
  have hstep := st308_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p168 : ((48224986748373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT308 (i+1))
      = (∑ i ∈ Finset.range 167, stT308 (i+1)) + stT308 168 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 167
    simpa using h
  have hprev := st308_p167
  have hstep := st308_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p169 : ((9545897627637/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT308 (i+1))
      = (∑ i ∈ Finset.range 168, stT308 (i+1)) + stT308 169 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 168
    simpa using h
  have hprev := st308_p168
  have hstep := st308_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p170 : ((48418861458161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT308 (i+1))
      = (∑ i ∈ Finset.range 169, stT308 (i+1)) + stT308 170 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 169
    simpa using h
  have hprev := st308_p169
  have hstep := st308_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p171 : ((48584036173847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT308 (i+1))
      = (∑ i ∈ Finset.range 170, stT308 (i+1)) + stT308 171 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 170
    simpa using h
  have hprev := st308_p170
  have hstep := st308_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p172 : ((23910743755929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT308 (i+1))
      = (∑ i ∈ Finset.range 171, stT308 (i+1)) + stT308 172 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 171
    simpa using h
  have hprev := st308_p171
  have hstep := st308_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p173 : ((23994413120179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT308 (i+1))
      = (∑ i ∈ Finset.range 172, stT308 (i+1)) + stT308 173 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 172
    simpa using h
  have hprev := st308_p172
  have hstep := st308_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p174 : ((12169738861993/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT308 (i+1))
      = (∑ i ∈ Finset.range 173, stT308 (i+1)) + stT308 174 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 173
    simpa using h
  have hprev := st308_p173
  have hstep := st308_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p175 : ((24119613506549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT308 (i+1))
      = (∑ i ∈ Finset.range 174, stT308 (i+1)) + stT308 175 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 174
    simpa using h
  have hprev := st308_p174
  have hstep := st308_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p176 : ((47716638816409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT308 (i+1))
      = (∑ i ∈ Finset.range 175, stT308 (i+1)) + stT308 176 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 175
    simpa using h
  have hprev := st308_p175
  have hstep := st308_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p177 : ((48340451629543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT308 (i+1))
      = (∑ i ∈ Finset.range 176, stT308 (i+1)) + stT308 177 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 176
    simpa using h
  have hprev := st308_p176
  have hstep := st308_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p178 : ((24325470549319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT308 (i+1))
      = (∑ i ∈ Finset.range 177, stT308 (i+1)) + stT308 178 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 177
    simpa using h
  have hprev := st308_p177
  have hstep := st308_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p179 : ((4793101223831/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT308 (i+1))
      = (∑ i ∈ Finset.range 178, stT308 (i+1)) + stT308 179 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 178
    simpa using h
  have hprev := st308_p178
  have hstep := st308_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p180 : ((4783620668189/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT308 (i+1))
      = (∑ i ∈ Finset.range 179, stT308 (i+1)) + stT308 180 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 179
    simpa using h
  have hprev := st308_p179
  have hstep := st308_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p181 : ((12144850455947/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT308 (i+1))
      = (∑ i ∈ Finset.range 180, stT308 (i+1)) + stT308 181 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 180
    simpa using h
  have hprev := st308_p180
  have hstep := st308_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p182 : ((24240036050019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT308 (i+1))
      = (∑ i ∈ Finset.range 181, stT308 (i+1)) + stT308 182 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 181
    simpa using h
  have hprev := st308_p181
  have hstep := st308_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p183 : ((23881987960543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT308 (i+1))
      = (∑ i ∈ Finset.range 182, stT308 (i+1)) + stT308 183 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 182
    simpa using h
  have hprev := st308_p182
  have hstep := st308_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p184 : ((48022826956793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT308 (i+1))
      = (∑ i ∈ Finset.range 183, stT308 (i+1)) + stT308 184 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 183
    simpa using h
  have hprev := st308_p183
  have hstep := st308_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p185 : ((48682366850201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT308 (i+1))
      = (∑ i ∈ Finset.range 184, stT308 (i+1)) + stT308 185 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 184
    simpa using h
  have hprev := st308_p184
  have hstep := st308_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p186 : ((48300891289133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT308 (i+1))
      = (∑ i ∈ Finset.range 185, stT308 (i+1)) + stT308 186 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 185
    simpa using h
  have hprev := st308_p185
  have hstep := st308_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p187 : ((9541791594329/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT308 (i+1))
      = (∑ i ∈ Finset.range 186, stT308 (i+1)) + stT308 187 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 186
    simpa using h
  have hprev := st308_p186
  have hstep := st308_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p188 : ((48178506244057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT308 (i+1))
      = (∑ i ∈ Finset.range 187, stT308 (i+1)) + stT308 188 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 187
    simpa using h
  have hprev := st308_p187
  have hstep := st308_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p189 : ((48704280456889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT308 (i+1))
      = (∑ i ∈ Finset.range 188, stT308 (i+1)) + stT308 189 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 188
    simpa using h
  have hprev := st308_p188
  have hstep := st308_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p190 : ((48175118984043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT308 (i+1))
      = (∑ i ∈ Finset.range 189, stT308 (i+1)) + stT308 190 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 189
    simpa using h
  have hprev := st308_p189
  have hstep := st308_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p191 : ((23852389295909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT308 (i+1))
      = (∑ i ∈ Finset.range 190, stT308 (i+1)) + stT308 191 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 190
    simpa using h
  have hprev := st308_p190
  have hstep := st308_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p192 : ((48270410159999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT308 (i+1))
      = (∑ i ∈ Finset.range 191, stT308 (i+1)) + stT308 192 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 191
    simpa using h
  have hprev := st308_p191
  have hstep := st308_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p193 : ((48700630628829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT308 (i+1))
      = (∑ i ∈ Finset.range 192, stT308 (i+1)) + stT308 193 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 192
    simpa using h
  have hprev := st308_p192
  have hstep := st308_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p194 : ((48116137335093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT308 (i+1))
      = (∑ i ∈ Finset.range 193, stT308 (i+1)) + stT308 194 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 193
    simpa using h
  have hprev := st308_p193
  have hstep := st308_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p195 : ((47707572244143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT308 (i+1))
      = (∑ i ∈ Finset.range 194, stT308 (i+1)) + stT308 195 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 194
    simpa using h
  have hprev := st308_p194
  have hstep := st308_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p196 : ((1509252082989/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT308 (i+1))
      = (∑ i ∈ Finset.range 195, stT308 (i+1)) + stT308 196 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 195
    simpa using h
  have hprev := st308_p195
  have hstep := st308_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p197 : ((24350824020159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT308 (i+1))
      = (∑ i ∈ Finset.range 196, stT308 (i+1)) + stT308 197 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 196
    simpa using h
  have hprev := st308_p196
  have hstep := st308_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p198 : ((24060976549989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT308 (i+1))
      = (∑ i ∈ Finset.range 197, stT308 (i+1)) + stT308 198 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 197
    simpa using h
  have hprev := st308_p197
  have hstep := st308_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p199 : ((23850357783441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT308 (i+1))
      = (∑ i ∈ Finset.range 198, stT308 (i+1)) + stT308 199 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 198
    simpa using h
  have hprev := st308_p198
  have hstep := st308_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p200 : ((6032236823601/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT308 (i+1))
      = (∑ i ∈ Finset.range 199, stT308 (i+1)) + stT308 200 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 199
    simpa using h
  have hprev := st308_p199
  have hstep := st308_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p201 : ((24355500581679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT308 (i+1))
      = (∑ i ∈ Finset.range 200, stT308 (i+1)) + stT308 201 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 200
    simpa using h
  have hprev := st308_p200
  have hstep := st308_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p202 : ((24095679430229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT308 (i+1))
      = (∑ i ∈ Finset.range 201, stT308 (i+1)) + stT308 202 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 201
    simpa using h
  have hprev := st308_p201
  have hstep := st308_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p203 : ((23846401555971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT308 (i+1))
      = (∑ i ∈ Finset.range 202, stT308 (i+1)) + stT308 203 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 202
    simpa using h
  have hprev := st308_p202
  have hstep := st308_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p204 : ((24078165399471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT308 (i+1))
      = (∑ i ∈ Finset.range 203, stT308 (i+1)) + stT308 204 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 203
    simpa using h
  have hprev := st308_p203
  have hstep := st308_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p205 : ((24354219856971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT308 (i+1))
      = (∑ i ∈ Finset.range 204, stT308 (i+1)) + stT308 205 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 204
    simpa using h
  have hprev := st308_p204
  have hstep := st308_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p206 : ((24161236383449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT308 (i+1))
      = (∑ i ∈ Finset.range 205, stT308 (i+1)) + stT308 206 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 205
    simpa using h
  have hprev := st308_p205
  have hstep := st308_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p207 : ((47715032608201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT308 (i+1))
      = (∑ i ∈ Finset.range 206, stT308 (i+1)) + stT308 207 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 206
    simpa using h
  have hprev := st308_p206
  have hstep := st308_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p208 : ((23999250127913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT308 (i+1))
      = (∑ i ∈ Finset.range 207, stT308 (i+1)) + stT308 208 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 207
    simpa using h
  have hprev := st308_p207
  have hstep := st308_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p209 : ((6081666767561/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT308 (i+1))
      = (∑ i ∈ Finset.range 208, stT308 (i+1)) + stT308 209 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 208
    simpa using h
  have hprev := st308_p208
  have hstep := st308_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p210 : ((6062237959331/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT308 (i+1))
      = (∑ i ∈ Finset.range 209, stT308 (i+1)) + stT308 210 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 209
    simpa using h
  have hprev := st308_p209
  have hstep := st308_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p211 : ((47814313642089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT308 (i+1))
      = (∑ i ∈ Finset.range 210, stT308 (i+1)) + stT308 211 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 210
    simpa using h
  have hprev := st308_p210
  have hstep := st308_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p212 : ((47817633642957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT308 (i+1))
      = (∑ i ∈ Finset.range 211, stT308 (i+1)) + stT308 212 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 211
    simpa using h
  have hprev := st308_p211
  have hstep := st308_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p213 : ((48498113031021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT308 (i+1))
      = (∑ i ∈ Finset.range 212, stT308 (i+1)) + stT308 213 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 212
    simpa using h
  have hprev := st308_p212
  have hstep := st308_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p214 : ((24331793884193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT308 (i+1))
      = (∑ i ∈ Finset.range 213, stT308 (i+1)) + stT308 214 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 213
    simpa using h
  have hprev := st308_p213
  have hstep := st308_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p215 : ((3001878032071/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT308 (i+1))
      = (∑ i ∈ Finset.range 214, stT308 (i+1)) + stT308 215 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 214
    simpa using h
  have hprev := st308_p214
  have hstep := st308_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p216 : ((23845636892303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT308 (i+1))
      = (∑ i ∈ Finset.range 215, stT308 (i+1)) + stT308 216 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 215
    simpa using h
  have hprev := st308_p215
  have hstep := st308_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p217 : ((24111811624703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT308 (i+1))
      = (∑ i ∈ Finset.range 216, stT308 (i+1)) + stT308 217 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 216
    simpa using h
  have hprev := st308_p216
  have hstep := st308_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p218 : ((24360281754373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT308 (i+1))
      = (∑ i ∈ Finset.range 217, stT308 (i+1)) + stT308 218 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 217
    simpa using h
  have hprev := st308_p217
  have hstep := st308_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p219 : ((24173482768867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT308 (i+1))
      = (∑ i ∈ Finset.range 218, stT308 (i+1)) + stT308 219 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 218
    simpa using h
  have hprev := st308_p218
  have hstep := st308_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p220 : ((23865383481867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT308 (i+1))
      = (∑ i ∈ Finset.range 219, stT308 (i+1)) + stT308 220 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 219
    simpa using h
  have hprev := st308_p219
  have hstep := st308_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p221 : ((23946644613819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT308 (i+1))
      = (∑ i ∈ Finset.range 220, stT308 (i+1)) + stT308 221 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 220
    simpa using h
  have hprev := st308_p220
  have hstep := st308_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p222 : ((24281505819211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT308 (i+1))
      = (∑ i ∈ Finset.range 221, stT308 (i+1)) + stT308 222 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 221
    simpa using h
  have hprev := st308_p221
  have hstep := st308_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p223 : ((24322450837667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT308 (i+1))
      = (∑ i ∈ Finset.range 222, stT308 (i+1)) + stT308 223 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 222
    simpa using h
  have hprev := st308_p222
  have hstep := st308_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p224 : ((24004820448377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT308 (i+1))
      = (∑ i ∈ Finset.range 223, stT308 (i+1)) + stT308 224 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 223
    simpa using h
  have hprev := st308_p223
  have hstep := st308_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p225 : ((47681653399427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT308 (i+1))
      = (∑ i ∈ Finset.range 224, stT308 (i+1)) + stT308 225 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 224
    simpa using h
  have hprev := st308_p224
  have hstep := st308_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p226 : ((48182029938317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT308 (i+1))
      = (∑ i ∈ Finset.range 225, stT308 (i+1)) + stT308 226 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 225
    simpa using h
  have hprev := st308_p225
  have hstep := st308_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p227 : ((48714082242131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT308 (i+1))
      = (∑ i ∈ Finset.range 226, stT308 (i+1)) + stT308 227 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 226
    simpa using h
  have hprev := st308_p226
  have hstep := st308_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p228 : ((1937669845237/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT308 (i+1))
      = (∑ i ∈ Finset.range 227, stT308 (i+1)) + stT308 228 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 227
    simpa using h
  have hprev := st308_p227
  have hstep := st308_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p229 : ((47794140867649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT308 (i+1))
      = (∑ i ∈ Finset.range 228, stT308 (i+1)) + stT308 229 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 228
    simpa using h
  have hprev := st308_p228
  have hstep := st308_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p230 : ((59719573847/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT308 (i+1))
      = (∑ i ∈ Finset.range 229, stT308 (i+1)) + stT308 230 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 229
    simpa using h
  have hprev := st308_p229
  have hstep := st308_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p231 : ((12102751378261/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT308 (i+1))
      = (∑ i ∈ Finset.range 230, stT308 (i+1)) + stT308 231 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 230
    simpa using h
  have hprev := st308_p230
  have hstep := st308_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p232 : ((3045459100579/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT308 (i+1))
      = (∑ i ∈ Finset.range 231, stT308 (i+1)) + stT308 232 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 231
    simpa using h
  have hprev := st308_p231
  have hstep := st308_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p233 : ((24123726183107/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT308 (i+1))
      = (∑ i ∈ Finset.range 232, stT308 (i+1)) + stT308 233 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 232
    simpa using h
  have hprev := st308_p232
  have hstep := st308_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p234 : ((9539414447123/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT308 (i+1))
      = (∑ i ∈ Finset.range 233, stT308 (i+1)) + stT308 234 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 233
    simpa using h
  have hprev := st308_p233
  have hstep := st308_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p235 : ((47897738765663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT308 (i+1))
      = (∑ i ∈ Finset.range 234, stT308 (i+1)) + stT308 235 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 234
    simpa using h
  have hprev := st308_p234
  have hstep := st308_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p236 : ((48547808547871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT308 (i+1))
      = (∑ i ∈ Finset.range 235, stT308 (i+1)) + stT308 236 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 235
    simpa using h
  have hprev := st308_p235
  have hstep := st308_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p237 : ((24344313331337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT308 (i+1))
      = (∑ i ∈ Finset.range 236, stT308 (i+1)) + stT308 237 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 236
    simpa using h
  have hprev := st308_p236
  have hstep := st308_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p238 : ((24058710435611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT308 (i+1))
      = (∑ i ∈ Finset.range 237, stT308 (i+1)) + stT308 238 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 237
    simpa using h
  have hprev := st308_p237
  have hstep := st308_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p239 : ((23833074677683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT308 (i+1))
      = (∑ i ∈ Finset.range 238, stT308 (i+1)) + stT308 239 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 238
    simpa using h
  have hprev := st308_p238
  have hstep := st308_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p240 : ((47983482781033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT308 (i+1))
      = (∑ i ∈ Finset.range 239, stT308 (i+1)) + stT308 240 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 239
    simpa using h
  have hprev := st308_p239
  have hstep := st308_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p241 : ((48611492366737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT308 (i+1))
      = (∑ i ∈ Finset.range 240, stT308 (i+1)) + stT308 241 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 240
    simpa using h
  have hprev := st308_p240
  have hstep := st308_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p242 : ((48657356573489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT308 (i+1))
      = (∑ i ∈ Finset.range 241, stT308 (i+1)) + stT308 242 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 241
    simpa using h
  have hprev := st308_p241
  have hstep := st308_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p243 : ((24029858460681/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT308 (i+1))
      = (∑ i ∈ Finset.range 242, stT308 (i+1)) + stT308 243 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 242
    simpa using h
  have hprev := st308_p242
  have hstep := st308_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p244 : ((23829026024331/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT308 (i+1))
      = (∑ i ∈ Finset.range 243, stT308 (i+1)) + stT308 244 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 243
    simpa using h
  have hprev := st308_p243
  have hstep := st308_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p245 : ((24004480220773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT308 (i+1))
      = (∑ i ∈ Finset.range 244, stT308 (i+1)) + stT308 245 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 244
    simpa using h
  have hprev := st308_p244
  have hstep := st308_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p246 : ((24312075574093/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT308 (i+1))
      = (∑ i ∈ Finset.range 245, stT308 (i+1)) + stT308 246 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 245
    simpa using h
  have hprev := st308_p245
  have hstep := st308_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p247 : ((24329821534853/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT308 (i+1))
      = (∑ i ∈ Finset.range 246, stT308 (i+1)) + stT308 247 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 246
    simpa using h
  have hprev := st308_p246
  have hstep := st308_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p248 : ((48070411036783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT308 (i+1))
      = (∑ i ∈ Finset.range 247, stT308 (i+1)) + stT308 248 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 247
    simpa using h
  have hprev := st308_p247
  have hstep := st308_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p249 : ((11913879879427/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT308 (i+1))
      = (∑ i ∈ Finset.range 248, stT308 (i+1)) + stT308 249 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 248
    simpa using h
  have hprev := st308_p248
  have hstep := st308_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_p250 : ((47970181691583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT308 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT308 (i+1))
      = (∑ i ∈ Finset.range 249, stT308 (i+1)) + stT308 250 := by
    have h := Finset.sum_range_succ (fun i => stT308 (i+1)) 249
    simpa using h
  have hprev := st308_p249
  have hstep := st308_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st308_s250 :
    |Real.sin (((308 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))
      - ((-13553/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -656211/2500000) (δ := 15447/1000000000) (ψ := -270827/250000) 308 271
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 308`** (evaluated boundary). -/
theorem station_308_sign : 0 < hardyG ((((308:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 308 250 (by norm_num) (by norm_num)
    ((-270827/250000 : ℚ) : ℝ)
  have hchain := st308_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT308 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((308 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-270827/250000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st308_c250
  have hsinb := abs_le.mp st308_s250
  have hbdy_lo : ((67515095808177/1517828000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((308 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-270827/250000 : ℚ) : ℝ))) / 2
          - ((((308:ℕ)):ℝ))
            * Real.sin (((308 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-270827/250000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((308:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((308:ℝ) * Real.log (250:ℝ) - ((-270827/250000 : ℚ) : ℝ))) / 2
        - ((308:ℝ)) * Real.sin ((308:ℝ) * Real.log (250:ℝ) - ((-270827/250000 : ℚ) : ℝ))
        ≥ ((533754147/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((308:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((533754147/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((533754147/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((533754147/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((308:ℕ)):ℝ))+1) * (((((308:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((128948212503/62500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((47970181691583/10000000000000 : ℚ) : ℝ) + ((67515095808177/1517828000000000 : ℚ) : ℝ)
      - ((128948212503/62500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-270827/250000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((308:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-270827/250000 : ℚ) : ℝ)
        * (riemannZeta (line ((((308:ℕ)):ℝ)))).re
      - Real.sin ((-270827/250000 : ℚ) : ℝ)
        * (riemannZeta (line ((((308:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((308:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((308:ℕ)):ℝ))
      = (((((308:ℕ)):ℝ)) * (Real.log ((((308:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((308:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_308
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
  have hθwin : |(((-270827/250000 : ℚ) : ℝ) + ((71:ℤ)) * (2*Real.pi)) - theta ((((308:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((308:ℕ)):ℝ)))
    (φ := ((-270827/250000 : ℚ) : ℝ) + ((71:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-270827/250000 : ℚ)) : ℝ) 71).1,
    (cos_sin_shift (((-270827/250000 : ℚ)) : ℝ) 71).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_308_sign
end AxiomAudit
