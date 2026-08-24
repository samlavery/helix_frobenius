import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 286` (rung-290.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT286 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((286 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((487099/1000000 : ℚ) : ℝ))

theorem st286_c1 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((441847/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -304437/2500000) (δ := 201/1000000000) (ψ := 487099/1000000) 286 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t1 : ((441797/500000 : ℚ) : ℝ) ≤ stT286 1 := by
  have hc : ((441797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((441797/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((441797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c2 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-986029/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7435603/10000000) (δ := 14479/1000000000) (ψ := 487099/1000000) 286 31
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t2 : ((-1743246303943/2500000000000 : ℚ) : ℝ) ≤ stT286 2 := by
  have hc : ((-986129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1743246303943/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-986129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c3 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((451679/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -138519/1250000) (δ := 359/25000000) (ψ := 487099/1000000) 286 50
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t3 : ((1303740467379/2500000000000 : ℚ) : ℝ) ≤ stT286 3 := by
  have hc : ((451629/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1303740467379/2500000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((451629/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c4 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((123551/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 381027/10000000) (δ := 7177/500000000) (ψ := 487099/1000000) 286 63
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t4 : ((247077/500000 : ℚ) : ℝ) ≤ stT286 4 := by
  have hc : ((247077/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((247077/500000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((247077/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c5 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((417933/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 712267/2500000) (δ := 14377/1000000000) (ψ := 487099/1000000) 286 73
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t5 : ((373721116691/2000000000000 : ℚ) : ℝ) ≤ stT286 5 := by
  have hc : ((417833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((373721116691/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((417833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c6 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-15506/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1509047/2000000) (δ := 14483/1000000000) (ψ := 487099/1000000) 286 81
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t6 : ((-1012949764443/2500000000000 : ℚ) : ℝ) ≤ stT286 6 := by
  have hc : ((-248121/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1012949764443/2500000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-248121/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c7 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-39993/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3903621/5000000) (δ := 1437/100000000) (ψ := 487099/1000000) 286 88
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t7 : ((-30234892213/80000000000 : ℚ) : ℝ) ≤ stT286 7 := by
  have hc : ((-39997/40000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30234892213/80000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-39997/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c8 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-445291/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -133471/200000) (δ := 14419/1000000000) (ψ := 487099/1000000) 286 95
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t8 : ((-787259123547/2500000000000 : ℚ) : ℝ) ≤ stT286 8 := by
  have hc : ((-445341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-787259123547/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-445341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c9 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((921291/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -998521/10000000) (δ := 14319/1000000000) (ψ := 487099/1000000) 286 100
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t9 : ((3070636359603/10000000000000 : ℚ) : ℝ) ≤ stT286 9 := by
  have hc : ((921191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3070636359603/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((921191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c10 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-22241/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -210279/500000) (δ := 3587/250000000) (ψ := 487099/1000000) 286 105
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t10 : ((-35197735279/1000000000000 : ℚ) : ℝ) ≤ stT286 10 := by
  have hc : ((-22261/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35197735279/1000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-22261/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c11 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((903151/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13867/125000) (δ := 14319/1000000000) (ψ := 487099/1000000) 286 109
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t11 : ((2722800809763/10000000000000 : ℚ) : ℝ) ≤ stT286 11 := by
  have hc : ((903051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2722800809763/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((903051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c12 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((490401/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 245329/5000000) (δ := 14313/1000000000) (ψ := 487099/1000000) 286 113
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t12 : ((1415521239601/5000000000000 : ℚ) : ℝ) ≤ stT286 12 := by
  have hc : ((490351/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1415521239601/5000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((490351/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c13 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-455977/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1022133/2000000) (δ := 14461/1000000000) (ψ := 487099/1000000) 286 117
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t13 : ((-1264930015577/10000000000000 : ℚ) : ℝ) ≤ stT286 13 := by
  have hc : ((-456077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1264930015577/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-456077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c14 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((955021/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 376333/5000000) (δ := 14463/1000000000) (ψ := 487099/1000000) 286 120
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t14 : ((638033330913/2500000000000 : ℚ) : ℝ) ≤ stT286 14 := by
  have hc : ((954921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((638033330913/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((954921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c15 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((75541/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2958699/10000000) (δ := 7209/500000000) (ψ := 487099/1000000) 286 123
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t15 : ((48748578937/500000000000 : ℚ) : ℝ) ≤ stT286 15 := by
  have hc : ((75521/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48748578937/500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((75521/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c16 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((70247/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1979837/10000000) (δ := 7153/500000000) (ψ := 487099/1000000) 286 126
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t16 : ((70237/400000 : ℚ) : ℝ) ≤ stT286 16 := by
  have hc : ((70237/100000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70237/400000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((70237/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c17 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((376237/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -224683/1250000) (δ := 23/1600000) (ψ := 487099/1000000) 286 129
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t17 : ((228096849393/1250000000000 : ℚ) : ℝ) ≤ stT286 17 := by
  have hc : ((376187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228096849393/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((376187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c18 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-99683/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3827433/5000000) (δ := 7221/500000000) (ψ := 487099/1000000) 286 131
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t18 : ((-234978693939/1000000000000 : ℚ) : ℝ) ≤ stT286 18 := by
  have hc : ((-99693/100000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234978693939/1000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-99693/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c19 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((189569/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25343/312500) (δ := 3591/250000000) (ψ := 487099/1000000) 286 134
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t19 : ((434855165193/2000000000000 : ℚ) : ℝ) ≤ stT286 19 := by
  have hc : ((189549/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((434855165193/2000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((189549/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c20 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-206823/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4447807/10000000) (δ := 7189/500000000) (ψ := 487099/1000000) 286 136
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t20 : ((-115673474691/2500000000000 : ℚ) : ℝ) ≤ stT286 20 := by
  have hc : ((-206923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115673474691/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-206923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c21 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-249921/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -779109/1000000) (δ := 447/31250000) (ψ := 487099/1000000) 286 139
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t21 : ((-272713456167/1250000000000 : ℚ) : ℝ) ≤ stT286 21 := by
  have hc : ((-124973/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-272713456167/1250000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-124973/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c22 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-45151/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5945217/10000000) (δ := 14489/1000000000) (ψ := 487099/1000000) 286 141
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t22 : ((-48137809129/312500000000 : ℚ) : ℝ) ≤ stT286 22 := by
  have hc : ((-180629/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48137809129/312500000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-180629/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c23 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-613469/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2789053/5000000) (δ := 1791/125000000) (ψ := 487099/1000000) 286 143
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t23 : ((-255876066501/2000000000000 : ℚ) : ℝ) ≤ stT286 23 := by
  have hc : ((-613569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-255876066501/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-613569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c24 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-869787/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6563919/10000000) (δ := 723/50000000) (ψ := 487099/1000000) 286 145
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t24 : ((-887824939827/5000000000000 : ℚ) : ℝ) ≤ stT286 24 := by
  have hc : ((-869887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-887824939827/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-869887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c25 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-186083/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 864481/1250000) (δ := 14353/1000000000) (ψ := 487099/1000000) 286 146
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t25 : ((-372206186103/2000000000000 : ℚ) : ℝ) ≤ stT286 25 := by
  have hc : ((-186103/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-372206186103/2000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-186103/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c26 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((153103/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1771361/5000000) (δ := 14339/1000000000) (ψ := 487099/1000000) 286 148
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t26 : ((300063516483/10000000000000 : ℚ) : ℝ) ≤ stT286 26 := by
  have hc : ((153003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((300063516483/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((153003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c27 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((937453/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -88889/1000000) (δ := 573/40000000) (ψ := 487099/1000000) 286 150
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t27 : ((3607871697/20000000000 : ℚ) : ℝ) ≤ stT286 27 := by
  have hc : ((937353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3607871697/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((937353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c28 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-813397/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6301911/10000000) (δ := 1431/100000000) (ψ := 487099/1000000) 286 152
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t28 : ((-1537365341031/10000000000000 : ℚ) : ℝ) ≤ stT286 28 := by
  have hc : ((-813497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1537365341031/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-813497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c29 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((332199/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 616081/2000000) (δ := 14403/1000000000) (ψ := 487099/1000000) 286 153
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t29 : ((616692234347/10000000000000 : ℚ) : ℝ) ≤ stT286 29 := by
  have hc : ((332099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((616692234347/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((332099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c30 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-16883/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4095949/10000000) (δ := 14389/1000000000) (ψ := 487099/1000000) 286 155
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t30 : ((-3858705717/312500000000 : ℚ) : ℝ) ≤ stT286 30 := by
  have hc : ((-4227/62500 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3858705717/312500000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-4227/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c31 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((571/5000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1820433/5000000) (δ := 14481/1000000000) (ψ := 487099/1000000) 286 156
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t31 : ((2049296473/100000000000 : ℚ) : ℝ) ≤ stT286 31 := by
  have hc : ((1141/10000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2049296473/100000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((1141/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c32 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-443141/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -253737/500000) (δ := 14467/1000000000) (ψ := 487099/1000000) 286 158
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t32 : ((-783546812847/10000000000000 : ℚ) : ℝ) ≤ stT286 32 := by
  have hc : ((-443241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-783546812847/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-443241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c33 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((441731/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1218991/10000000) (δ := 359/25000000) (ψ := 487099/1000000) 286 159
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t33 : ((96108460557/625000000000 : ℚ) : ℝ) ≤ stT286 33 := by
  have hc : ((441681/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96108460557/625000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((441681/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c34 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-921363/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6855923/10000000) (δ := 287/20000000) (ψ := 487099/1000000) 286 160
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t34 : ((-790148072259/5000000000000 : ℚ) : ℝ) ≤ stT286 34 := by
  have hc : ((-921463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-790148072259/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-921463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c35 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((37211/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3833941/10000000) (δ := 2873/200000000) (ψ := 487099/1000000) 286 162
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t35 : ((15682255047/2500000000000 : ℚ) : ℝ) ≤ stT286 35 := by
  have hc : ((37111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15682255047/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((37111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c36 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((97131/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 600289/10000000) (δ := 14331/1000000000) (ψ := 487099/1000000) 286 163
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t36 : ((80934134293/500000000000 : ℚ) : ℝ) ≤ stT286 36 := by
  have hc : ((97121/100000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80934134293/500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((97121/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c37 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-220423/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4482611/10000000) (δ := 14379/1000000000) (ψ := 487099/1000000) 286 164
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t37 : ((-36253760677/1000000000000 : ℚ) : ℝ) ≤ stT286 37 := by
  have hc : ((-220523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36253760677/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-220523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c38 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-999989/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7842411/10000000) (δ := 7243/500000000) (ψ := 487099/1000000) 286 165
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t38 : ((-324471875427/2000000000000 : ℚ) : ℝ) ≤ stT286 38 := by
  have hc : ((-1000089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324471875427/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-1000089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c39 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-416523/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5001033/10000000) (δ := 29/2000000) (ψ := 487099/1000000) 286 167
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t39 : ((-333565455343/5000000000000 : ℚ) : ℝ) ≤ stT286 39 := by
  have hc : ((-416623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333565455343/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-416623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c40 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((503883/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -260677/1000000) (δ := 2879/200000000) (ψ := 487099/1000000) 286 168
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t40 : ((398275222527/5000000000000 : ℚ) : ℝ) ≤ stT286 40 := by
  have hc : ((503783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((398275222527/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((503783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c41 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((241351/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -164881/2500000) (δ := 2863/200000000) (ψ := 487099/1000000) 286 169
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t41 : ((188443871631/1250000000000 : ℚ) : ℝ) ≤ stT286 41 := by
  have hc : ((120663/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188443871631/1250000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((120663/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c42 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((941103/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 862297/10000000) (δ := 7211/500000000) (ψ := 487099/1000000) 286 170
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t42 : ((1451998682099/10000000000000 : ℚ) : ℝ) ≤ stT286 42 := by
  have hc : ((941003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1451998682099/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((941003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c43 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((70281/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1978641/10000000) (δ := 14329/1000000000) (ψ := 487099/1000000) 286 171
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t43 : ((21432444187/200000000000 : ℚ) : ℝ) ≤ stT286 43 := by
  have hc : ((70271/100000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21432444187/200000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((70271/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c44 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((117111/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 270817/1000000) (δ := 14367/1000000000) (ψ := 487099/1000000) 286 172
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t44 : ((22064212727/312500000000 : ℚ) : ℝ) ≤ stT286 44 := by
  have hc : ((58543/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22064212727/312500000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((58543/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c45 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((168389/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3068259/10000000) (δ := 1793/125000000) (ψ := 487099/1000000) 286 173
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t45 : ((250944799029/5000000000000 : ℚ) : ℝ) ≤ stT286 45 := by
  have hc : ((168339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250944799029/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((168339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c46 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((334159/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3075209/10000000) (δ := 897/62500000) (ψ := 487099/1000000) 286 174
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t46 : ((492542936721/10000000000000 : ℚ) : ℝ) ≤ stT286 46 := by
  have hc : ((334059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((492542936721/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((334059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c47 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((91129/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10977/40000) (δ := 2889/200000000) (ψ := 487099/1000000) 286 175
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t47 : ((132896051741/2000000000000 : ℚ) : ℝ) ≤ stT286 47 := by
  have hc : ((91109/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132896051741/2000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((91109/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c48 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((335297/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 522367/2500000) (δ := 7169/500000000) (ψ := 487099/1000000) 286 176
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t48 : ((3871097109/40000000000 : ℚ) : ℝ) ≤ stT286 48 := by
  have hc : ((335247/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3871097109/40000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((335247/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c49 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((900581/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1124233/10000000) (δ := 3593/250000000) (ψ := 487099/1000000) 286 177
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t49 : ((1286401042651/10000000000000 : ℚ) : ℝ) ≤ stT286 49 := by
  have hc : ((900481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1286401042651/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((900481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c50 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((998461/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17341/1250000) (δ := 14479/1000000000) (ψ := 487099/1000000) 286 178
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t50 : ((1411895104893/10000000000000 : ℚ) : ℝ) ≤ stT286 50 := by
  have hc : ((998361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1411895104893/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((998361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c51 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((48789/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1687833/10000000) (δ := 901/62500000) (ψ := 487099/1000000) 286 179
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t51 : ((6830950917/62500000000 : ℚ) : ℝ) ≤ stT286 51 := by
  have hc : ((195131/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6830950917/62500000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((195131/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c52 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((165293/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1755927/5000000) (δ := 7247/500000000) (ψ := 487099/1000000) 286 180
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t52 : ((916325571/40000000000 : ℚ) : ℝ) ≤ stT286 52 := by
  have hc : ((165193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((916325571/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((165193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c53 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-620473/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1120071/2000000) (δ := 7201/500000000) (ψ := 487099/1000000) 286 181
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t53 : ((-426211398119/5000000000000 : ℚ) : ℝ) ≤ stT286 53 := by
  have hc : ((-620573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-426211398119/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-620573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c54 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-999359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7764497/10000000) (δ := 14401/1000000000) (ψ := 487099/1000000) 286 181
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t54 : ((-340022948013/2500000000000 : ℚ) : ℝ) ≤ stT286 54 := by
  have hc : ((-999459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-340022948013/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-999459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c55 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-479127/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 258807/500000) (δ := 3577/250000000) (ψ := 487099/1000000) 286 182
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t55 : ((-1615474217/25000000000 : ℚ) : ℝ) ≤ stT286 55 := by
  have hc : ((-479227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1615474217/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-479227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c56 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((294667/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 587851/2500000) (δ := 3597/250000000) (ψ := 487099/1000000) 286 183
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t56 : ((196849232401/2500000000000 : ℚ) : ℝ) ≤ stT286 56 := by
  have hc : ((294617/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196849232401/2500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((294617/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c57 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((960907/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -140269/2000000) (δ := 14323/1000000000) (ψ := 487099/1000000) 286 184
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t57 : ((318154904331/2500000000000 : ℚ) : ℝ) ≤ stT286 57 := by
  have hc : ((960807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((318154904331/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((960807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c58 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-18871/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3974171/10000000) (δ := 1443/100000000) (ψ := 487099/1000000) 286 185
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t58 : ((-4982031223/2000000000000 : ℚ) : ℝ) ≤ stT286 58 := by
  have hc : ((-18971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4982031223/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-18971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c59 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-197517/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7459639/10000000) (δ := 7233/500000000) (ψ := 487099/1000000) 286 186
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t59 : ((-25717144493/200000000000 : ℚ) : ℝ) ≤ stT286 59 := by
  have hc : ((-197537/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25717144493/200000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-197537/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c60 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-49903/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2278719/5000000) (δ := 14337/1000000000) (ψ := 487099/1000000) 286 186
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t60 : ((-12890068677/400000000000 : ℚ) : ℝ) ≤ stT286 60 := by
  have hc : ((-49923/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12890068677/400000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-49923/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c61 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((482261/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 166981/2500000) (δ := 14359/1000000000) (ψ := 487099/1000000) 286 187
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t61 : ((38587970853/312500000000 : ℚ) : ℝ) ≤ stT286 61 := by
  have hc : ((482211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38587970853/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((482211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c62 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((40769/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1706891/5000000) (δ := 3613/250000000) (ψ := 487099/1000000) 286 188
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t62 : ((51751270749/2000000000000 : ℚ) : ℝ) ≤ stT286 62 := by
  have hc : ((40749/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51751270749/2000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((40749/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c63 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-49881/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7681459/10000000) (δ := 2869/200000000) (ψ := 487099/1000000) 286 189
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t63 : ((-15712618363/125000000000 : ℚ) : ℝ) ≤ stT286 63 := by
  have hc : ((-24943/25000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15712618363/125000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-24943/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c64 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((27783/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 223661/625000) (δ := 7229/500000000) (ψ := 487099/1000000) 286 189
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t64 : ((27763/1600000 : ℚ) : ℝ) ≤ stT286 64 := by
  have hc : ((27763/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27763/1600000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((27763/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c65 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((228521/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -208777/2000000) (δ := 14437/1000000000) (ψ := 487099/1000000) 286 190
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t65 : ((17713395507/156250000000 : ℚ) : ℝ) ≤ stT286 65 := by
  have hc : ((14281/15625 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17713395507/156250000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((14281/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c66 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-691409/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1167117/2000000) (δ := 14473/1000000000) (ψ := 487099/1000000) 286 191
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t66 : ((-170237760147/2000000000000 : ℚ) : ℝ) ≤ stT286 66 := by
  have hc : ((-691509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170237760147/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-691509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c67 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-77111/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4916513/10000000) (δ := 1433/100000000) (ψ := 487099/1000000) 286 191
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t67 : ((-18846111409/400000000000 : ℚ) : ℝ) ≤ stT286 67 := by
  have hc : ((-77131/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18846111409/400000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-77131/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c68 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((199369/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -99327/5000000) (δ := 14423/1000000000) (ψ := 487099/1000000) 286 192
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t68 : ((120873073311/1000000000000 : ℚ) : ℝ) ≤ stT286 68 := by
  have hc : ((199349/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120873073311/1000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((199349/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c69 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-578259/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -218739/400000) (δ := 3579/250000000) (ψ := 487099/1000000) 286 193
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t69 : ((-696262687381/10000000000000 : ℚ) : ℝ) ≤ stT286 69 := by
  have hc : ((-578359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-696262687381/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-578359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c70 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-43681/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2409723/5000000) (δ := 14487/1000000000) (ψ := 487099/1000000) 286 193
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t70 : ((-104447476623/2500000000000 : ℚ) : ℝ) ≤ stT286 70 := by
  have hc : ((-87387/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104447476623/2500000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-87387/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c71 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((477873/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -746529/10000000) (δ := 14409/1000000000) (ψ := 487099/1000000) 286 194
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t71 : ((567071257763/5000000000000 : ℚ) : ℝ) ≤ stT286 71 := by
  have hc : ((477823/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((567071257763/5000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((477823/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c72 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-21183/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -403393/625000) (δ := 14501/1000000000) (ψ := 487099/1000000) 286 195
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t72 : ((-3120920747/31250000000 : ℚ) : ℝ) ≤ stT286 72 := by
  have hc : ((-42371/50000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3120920747/31250000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-42371/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c73 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((206139/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1703961/5000000) (δ := 7151/500000000) (ψ := 487099/1000000) 286 195
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t73 : ((241150312029/10000000000000 : ℚ) : ℝ) ≤ stT286 73 := by
  have hc : ((206039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((241150312029/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((206039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c74 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((103167/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2572037/10000000) (δ := 14409/1000000000) (ψ := 487099/1000000) 286 196
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t74 : ((29976477993/500000000000 : ℚ) : ℝ) ≤ stT286 74 := by
  have hc : ((103147/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29976477993/500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((103147/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c75 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-945587/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7025479/10000000) (δ := 7197/500000000) (ψ := 487099/1000000) 286 196
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t75 : ((-1091985724587/10000000000000 : ℚ) : ℝ) ≤ stT286 75 := by
  have hc : ((-945687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1091985724587/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-945687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c76 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((190151/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 393917/5000000) (δ := 3579/250000000) (ψ := 487099/1000000) 286 197
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t76 : ((109047543609/1000000000000 : ℚ) : ℝ) ≤ stT286 76 := by
  have hc : ((190131/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109047543609/1000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((190131/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c77 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-306019/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2786789/5000000) (δ := 719/50000000) (ψ := 487099/1000000) 286 198
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t77 : ((-174399034407/2500000000000 : ℚ) : ℝ) ≤ stT286 77 := by
  have hc : ((-306069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174399034407/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-306069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c78 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((54817/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3652353/10000000) (δ := 719/50000000) (ψ := 487099/1000000) 286 198
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t78 : ((62011414459/5000000000000 : ℚ) : ℝ) ≤ stT286 78 := by
  have hc : ((54767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62011414459/5000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((54767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c79 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((381951/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -117889/400000) (δ := 1433/100000000) (ψ := 487099/1000000) 286 199
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t79 : ((429615596037/10000000000000 : ℚ) : ℝ) ≤ stT286 79 := by
  have hc : ((381851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((429615596037/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((381851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c80 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-37493/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6046617/10000000) (δ := 1433/100000000) (ψ := 487099/1000000) 286 199
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t80 : ((-10481009733/125000000000 : ℚ) : ℝ) ≤ stT286 80 := by
  have hc : ((-18749/25000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10481009733/125000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-18749/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c81 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((237953/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -779259/10000000) (δ := 7183/500000000) (ψ := 487099/1000000) 286 200
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t81 : ((33045552251/312500000000 : ℚ) : ℝ) ≤ stT286 81 := by
  have hc : ((29741/31250 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33045552251/312500000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((29741/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c82 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-199687/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7714101/10000000) (δ := 7229/500000000) (ψ := 487099/1000000) 286 201
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t82 : ((-55134908853/500000000000 : ℚ) : ℝ) ≤ stT286 82 := by
  have hc : ((-199707/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55134908853/500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-199707/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c83 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((928263/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9527/100000) (δ := 7229/500000000) (ψ := 487099/1000000) 286 201
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t83 : ((509395345823/5000000000000 : ℚ) : ℝ) ≤ stT286 83 := by
  have hc : ((928163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((509395345823/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((928163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c84 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-787123/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1548079/2500000) (δ := 28751/1000000000) (ψ := 487099/1000000) 286 202
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t84 : ((-85893114307/1000000000000 : ℚ) : ℝ) ≤ stT286 84 := by
  have hc : ((-787223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85893114307/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-787223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c85 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((615539/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 567329/2500000) (δ := 14351/1000000000) (ψ := 487099/1000000) 286 202
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t85 : ((166884285557/2500000000000 : ℚ) : ℝ) ≤ stT286 85 := by
  have hc : ((615439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166884285557/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((615439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c86 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-88719/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5076007/10000000) (δ := 14359/1000000000) (ψ := 487099/1000000) 286 203
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t86 : ((-11961218549/250000000000 : ℚ) : ℝ) ≤ stT286 86 := by
  have hc : ((-88739/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11961218549/250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-88739/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c87 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((290531/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 797509/2500000) (δ := 3611/250000000) (ψ := 487099/1000000) 286 203
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t87 : ((19460910017/625000000000 : ℚ) : ℝ) ≤ stT286 87 := by
  have hc : ((290431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19460910017/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((290431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c88 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-8349/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2173203/5000000) (δ := 7233/500000000) (ψ := 487099/1000000) 286 204
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t88 : ((-1113174677/62500000000 : ℚ) : ℝ) ≤ stT286 88 := by
  have hc : ((-4177/25000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1113174677/62500000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-4177/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c89 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((9703/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29162/78125) (δ := 14337/1000000000) (ψ := 487099/1000000) 286 204
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t89 : ((20543801857/2500000000000 : ℚ) : ℝ) ≤ stT286 89 := by
  have hc : ((19381/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20543801857/2500000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((19381/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c90 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-23729/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1993159/5000000) (δ := 1443/100000000) (ψ := 487099/1000000) 286 205
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t90 : ((-25117982097/10000000000000 : ℚ) : ℝ) ≤ stT286 90 := by
  have hc : ((-23829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25117982097/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-23829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c91 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((2533/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156573/400000) (δ := 2863/100000000) (ψ := 487099/1000000) 286 205
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t91 : ((650722293/1250000000000 : ℚ) : ℝ) ≤ stT286 91 := by
  have hc : ((2483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((650722293/1250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((2483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c92 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-20949/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3979367/10000000) (δ := 181/12500000) (ψ := 487099/1000000) 286 206
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t92 : ((-21945119077/10000000000000 : ℚ) : ℝ) ≤ stT286 92 := by
  have hc : ((-21049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21945119077/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-21049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c93 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((70567/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1875213/5000000) (δ := 14323/1000000000) (ψ := 487099/1000000) 286 206
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t93 : ((73070826117/10000000000000 : ℚ) : ℝ) ≤ stT286 93 := by
  have hc : ((70467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73070826117/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((70467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c94 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-76381/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2155199/5000000) (δ := 2883/200000000) (ψ := 487099/1000000) 286 207
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t94 : ((-39416307441/2500000000000 : ℚ) : ℝ) ≤ stT286 94 := by
  have hc : ((-76431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39416307441/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-76431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c95 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((265261/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 813951/2500000) (δ := 3597/250000000) (ψ := 487099/1000000) 286 207
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t95 : ((136024676229/5000000000000 : ℚ) : ℝ) ≤ stT286 95 := by
  have hc : ((265161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136024676229/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((265161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c96 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-201721/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -248259/500000) (δ := 3577/250000000) (ψ := 487099/1000000) 286 208
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t96 : ((-205931719791/5000000000000 : ℚ) : ℝ) ≤ stT286 96 := by
  have hc : ((-201771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205931719791/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-201771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c97 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((558941/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1222111/5000000) (δ := 3577/250000000) (ψ := 487099/1000000) 286 208
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t97 : ((283708486993/5000000000000 : ℚ) : ℝ) ≤ stT286 97 := by
  have hc : ((558841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((283708486993/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((558841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c98 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-71829/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -741293/1250000) (δ := 14401/1000000000) (ψ := 487099/1000000) 286 209
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t98 : ((-72568381367/1000000000000 : ℚ) : ℝ) ≤ stT286 98 := by
  have hc : ((-71839/100000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72568381367/1000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-71839/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c99 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((431037/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 664311/5000000) (δ := 14401/1000000000) (ψ := 487099/1000000) 286 209
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t99 : ((433157881519/5000000000000 : ℚ) : ℝ) ≤ stT286 99 := by
  have hc : ((430987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((433157881519/5000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((430987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c100 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-965291/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7193377/10000000) (δ := 7247/500000000) (ψ := 487099/1000000) 286 210
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t100 : ((-965391/10000000 : ℚ) : ℝ) ≤ stT286 100 := by
  have hc : ((-965391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-965391/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-965391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c101 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((999503/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -78841/10000000) (δ := 7247/500000000) (ψ := 487099/1000000) 286 210
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t101 : ((994442962911/10000000000000 : ℚ) : ℝ) ≤ stT286 101 := by
  have hc : ((999403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((994442962911/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((999403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c102 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-937517/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3482777/5000000) (δ := 14309/1000000000) (ψ := 487099/1000000) 286 210
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t102 : ((-232094899329/2500000000000 : ℚ) : ℝ) ≤ stT286 102 := by
  have hc : ((-937617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232094899329/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-937617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c103 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((47531/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -883399/5000000) (δ := 14387/1000000000) (ψ := 487099/1000000) 286 211
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t103 : ((187310057571/2500000000000 : ℚ) : ℝ) ≤ stT286 103 := by
  have hc : ((190099/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187310057571/2500000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((190099/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c104 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-93381/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5141461/10000000) (δ := 901/62500000) (ψ := 487099/1000000) 286 211
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t104 : ((-91587245981/2000000000000 : ℚ) : ℝ) ≤ stT286 104 := by
  have hc : ((-93401/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91587245981/2000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-93401/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c105 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((10123/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -372431/1000000) (δ := 3581/250000000) (ψ := 487099/1000000) 286 212
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t105 : ((197336739/25000000000 : ℚ) : ℝ) ≤ stT286 105 := by
  have hc : ((20221/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197336739/25000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((20221/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c106 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((171267/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19081/62500) (δ := 14479/1000000000) (ψ := 487099/1000000) 286 212
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t106 : ((33260100769/1000000000000 : ℚ) : ℝ) ≤ stT286 106 := by
  have hc : ((171217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33260100769/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((171217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c107 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-721331/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -371331/625000) (δ := 3593/250000000) (ψ := 487099/1000000) 286 213
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t107 : ((-697434040647/10000000000000 : ℚ) : ℝ) ≤ stT286 107 := by
  have hc : ((-721431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-697434040647/10000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-721431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c108 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((959951/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4437/62500) (δ := 3593/250000000) (ψ := 487099/1000000) 286 213
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t108 : ((3694466499/40000000000 : ℚ) : ℝ) ≤ stT286 108 := by
  have hc : ((959851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3694466499/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((959851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c109 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-97553/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7299789/10000000) (δ := 3593/250000000) (ψ := 487099/1000000) 286 213
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t109 : ((-93448475601/1000000000000 : ℚ) : ℝ) ≤ stT286 109 := by
  have hc : ((-97563/100000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93448475601/1000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-97563/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c110 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((730751/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1878437/10000000) (δ := 2893/200000000) (ψ := 487099/1000000) 286 214
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t110 : ((348323981881/5000000000000 : ℚ) : ℝ) ≤ stT286 110 := by
  have hc : ((730651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348323981881/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((730651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c111 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-262971/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2296121/5000000) (δ := 7169/500000000) (ψ := 487099/1000000) 286 214
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t111 : ((-124847972109/5000000000000 : ℚ) : ℝ) ≤ stT286 111 := by
  have hc : ((-263071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124847972109/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-263071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c112 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-305509/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1175793/2500000) (δ := 2889/200000000) (ψ := 487099/1000000) 286 215
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t112 : ((-18048350713/625000000000 : ℚ) : ℝ) ≤ stT286 112 := by
  have hc : ((-305609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18048350713/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-305609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c113 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((197347/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1652463/10000000) (δ := 2889/200000000) (ψ := 487099/1000000) 286 215
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t113 : ((1160154699/15625000000 : ℚ) : ℝ) ≤ stT286 113 := by
  have hc : ((98661/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1160154699/15625000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((98661/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c114 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-999231/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3877961/5000000) (δ := 14451/1000000000) (ψ := 487099/1000000) 286 216
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t114 : ((-467979711983/5000000000000 : ℚ) : ℝ) ≤ stT286 114 := by
  have hc : ((-999331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-467979711983/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-999331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c115 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((822769/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -755663/5000000) (δ := 897/62500000) (ψ := 487099/1000000) 286 216
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t115 : ((95892766647/1250000000000 : ℚ) : ℝ) ≤ stT286 115 := by
  have hc : ((822669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95892766647/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((822669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c116 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-296343/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 584893/1250000) (δ := 897/62500000) (ψ := 487099/1000000) 286 216
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t116 : ((-275240507311/10000000000000 : ℚ) : ℝ) ≤ stT286 116 := by
  have hc : ((-296443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275240507311/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-296443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c117 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-94067/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2445701/5000000) (δ := 14459/1000000000) (ψ := 487099/1000000) 286 217
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t117 : ((-21747037023/625000000000 : ℚ) : ℝ) ≤ stT286 117 := by
  have hc : ((-23523/62500 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21747037023/625000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-23523/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c118 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((888147/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 298437/2500000) (δ := 1793/125000000) (ψ := 487099/1000000) 286 217
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t118 : ((408756489489/5000000000000 : ℚ) : ℝ) ≤ stT286 118 := by
  have hc : ((888047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((408756489489/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((888047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c119 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-193753/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 722749/1000000) (δ := 1793/125000000) (ψ := 487099/1000000) 286 217
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t119 : ((-177631515327/2000000000000 : ℚ) : ℝ) ≤ stT286 119 := by
  have hc : ((-193773/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177631515327/2000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-193773/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c120 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((108253/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2497139/10000000) (δ := 3609/250000000) (ψ := 487099/1000000) 286 218
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t120 : ((9880265871/200000000000 : ℚ) : ℝ) ≤ stT286 120 := by
  have hc : ((108233/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9880265871/200000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((108233/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c121 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((194939/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3436503/10000000) (δ := 3609/250000000) (ψ := 487099/1000000) 286 218
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t121 : ((17712618651/1000000000000 : ℚ) : ℝ) ≤ stT286 121 := by
  have hc : ((194839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17712618651/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((194839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c122 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-208161/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1596663/2500000) (δ := 7237/500000000) (ψ := 487099/1000000) 286 219
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t122 : ((-47120715147/625000000000 : ℚ) : ℝ) ≤ stT286 122 := by
  have hc : ((-104093/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47120715147/625000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-104093/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c123 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((975907/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -549893/10000000) (δ := 14329/1000000000) (ψ := 487099/1000000) 286 219
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t123 : ((879854921883/10000000000000 : ℚ) : ℝ) ≤ stT286 123 := by
  have hc : ((975807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((879854921883/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((975807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c124 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-501253/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1047921/2000000) (δ := 14329/1000000000) (ψ := 487099/1000000) 286 219
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t124 : ((-450228530531/10000000000000 : ℚ) : ℝ) ≤ stT286 124 := by
  have hc : ((-501353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-450228530531/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-501353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c125 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-156969/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -945067/2000000) (δ := 14381/1000000000) (ψ := 487099/1000000) 286 220
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t125 : ((-35110547533/1250000000000 : ℚ) : ℝ) ≤ stT286 125 := by
  have hc : ((-157019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35110547533/1250000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-157019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c126 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((14459/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 121491/1250000) (δ := 14381/1000000000) (ψ := 487099/1000000) 286 220
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t126 : ((20607515753/250000000000 : ℚ) : ℝ) ≤ stT286 126 := by
  have hc : ((231319/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20607515753/250000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((231319/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c127 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-881407/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3312037/5000000) (δ := 7211/500000000) (ψ := 487099/1000000) 286 220
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t127 : ((-782211406999/10000000000000 : ℚ) : ℝ) ≤ stT286 127 := by
  have hc : ((-881507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-782211406999/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-881507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c128 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((179419/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3476001/10000000) (δ := 2863/200000000) (ψ := 487099/1000000) 286 221
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t128 : ((158497015677/10000000000000 : ℚ) : ℝ) ≤ stT286 128 := by
  have hc : ((179319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158497015677/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((179319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c129 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((670949/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 130517/625000) (δ := 2863/200000000) (ψ := 487099/1000000) 286 221
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t129 : ((11812980041/200000000000 : ℚ) : ℝ) ≤ stT286 129 := by
  have hc : ((670849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11812980041/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((670849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c130 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-497611/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3804751/5000000) (δ := 2863/200000000) (ψ := 487099/1000000) 286 221
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t130 : ((-436478058999/5000000000000 : ℚ) : ℝ) ≤ stT286 130 := by
  have hc : ((-497661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-436478058999/5000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-497661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c131 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((249741/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -81859/312500) (δ := 1801/125000000) (ψ := 487099/1000000) 286 222
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t131 : ((27269503183/625000000000 : ℚ) : ℝ) ≤ stT286 131 := by
  have hc : ((249691/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27269503183/625000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((249691/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c132 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((214631/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2817801/10000000) (δ := 1801/125000000) (ψ := 487099/1000000) 286 222
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t132 : ((46692181857/1250000000000 : ℚ) : ℝ) ≤ stT286 132 := by
  have hc : ((214581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46692181857/1250000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((214581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c133 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-494823/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3746957/5000000) (δ := 14303/1000000000) (ψ := 487099/1000000) 286 223
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t133 : ((-42910932703/500000000000 : ℚ) : ℝ) ≤ stT286 133 := by
  have hc : ((-494873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42910932703/500000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-494873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c134 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((328019/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2138099/10000000) (δ := 28703/1000000000) (ψ := 487099/1000000) 286 223
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t134 : ((70830481023/1250000000000 : ℚ) : ℝ) ≤ stT286 134 := by
  have hc : ((327969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70830481023/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((327969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c135 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((295177/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 317789/1000000) (δ := 14303/1000000000) (ψ := 487099/1000000) 286 223
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t135 : ((126980780487/5000000000000 : ℚ) : ℝ) ≤ stT286 135 := by
  have hc : ((295077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126980780487/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((295077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c136 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-971273/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3626651/5000000) (δ := 14393/1000000000) (ψ := 487099/1000000) 286 224
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t136 : ((-832945547889/10000000000000 : ℚ) : ℝ) ≤ stT286 136 := by
  have hc : ((-971373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-832945547889/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-971373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c137 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((13847/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -100757/500000) (δ := 1441/100000000) (ψ := 487099/1000000) 286 224
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t137 : ((2365714533/40000000000 : ℚ) : ℝ) ≤ stT286 137 := by
  have hc : ((2769/4000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2365714533/40000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((2769/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c138 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((292519/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 79621/250000) (δ := 14393/1000000000) (ψ := 487099/1000000) 286 224
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t138 : ((31115428533/1250000000000 : ℚ) : ℝ) ≤ stT286 138 := by
  have hc : ((292419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31115428533/1250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((292419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c139 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-98059/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7360609/10000000) (δ := 7243/500000000) (ψ := 487099/1000000) 286 225
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t139 : ((-83181047041/1000000000000 : ℚ) : ℝ) ≤ stT286 139 := by
  have hc : ((-98069/100000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83181047041/1000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-98069/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c140 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((313129/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2235131/10000000) (δ := 14317/1000000000) (ψ := 487099/1000000) 286 225
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t140 : ((132299984583/2500000000000 : ℚ) : ℝ) ≤ stT286 140 := by
  have hc : ((313079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132299984583/2500000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((313079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c141 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((416209/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 285381/1000000) (δ := 14317/1000000000) (ψ := 487099/1000000) 286 225
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t141 : ((350426610459/10000000000000 : ℚ) : ℝ) ≤ stT286 141 := by
  have hc : ((416109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((350426610459/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((416109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c142 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-31243/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1560221/2000000) (δ := 1803/125000000) (ψ := 487099/1000000) 286 226
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t142 : ((-104884742679/1250000000000 : ℚ) : ℝ) ≤ stT286 142 := by
  have hc : ((-249969/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104884742679/1250000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-249969/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c143 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((220803/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2783521/10000000) (δ := 1803/125000000) (ψ := 487099/1000000) 286 226
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t143 : ((92301465113/2500000000000 : ℚ) : ℝ) ≤ stT286 143 := by
  have hc : ((220753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92301465113/2500000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((220753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c144 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((637451/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 549757/2500000) (δ := 1803/125000000) (ψ := 487099/1000000) 286 226
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t144 : ((531125620883/10000000000000 : ℚ) : ℝ) ≤ stT286 144 := by
  have hc : ((637351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((531125620883/10000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((637351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c145 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-960301/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1429437/2000000) (δ := 14379/1000000000) (ψ := 487099/1000000) 286 226
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t145 : ((-159513962491/2000000000000 : ℚ) : ℝ) ≤ stT286 145 := by
  have hc : ((-960401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159513962491/2000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-960401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c146 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((111899/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -729331/2000000) (δ := 1809/125000000) (ψ := 487099/1000000) 286 227
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t146 : ((18505082279/2000000000000 : ℚ) : ℝ) ≤ stT286 146 := by
  have hc : ((111799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18505082279/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((111799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c147 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((880659/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 154233/1250000) (δ := 14331/1000000000) (ψ := 487099/1000000) 286 227
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t147 : ((363136367687/5000000000000 : ℚ) : ℝ) ≤ stT286 147 := by
  have hc : ((880559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((363136367687/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((880559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c148 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-758979/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6081349/10000000) (δ := 1809/125000000) (ψ := 487099/1000000) 286 227
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t148 : ((-124791828521/2000000000000 : ℚ) : ℝ) ≤ stT286 148 := by
  have hc : ((-759079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124791828521/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-759079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c149 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-69311/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1202933/2500000) (δ := 7219/500000000) (ψ := 487099/1000000) 286 228
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t149 : ((-1774942931/62500000000 : ℚ) : ℝ) ≤ stT286 149 := by
  have hc : ((-69331/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1774942931/62500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-69331/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c150 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((249983/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29169/10000000) (δ := 2873/200000000) (ψ := 487099/1000000) 286 228
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t150 : ((6377803349/78125000000 : ℚ) : ℝ) ≤ stT286 150 := by
  have hc : ((124979/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6377803349/78125000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((124979/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c151 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-62513/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 118043/250000) (δ := 2873/200000000) (ψ := 487099/1000000) 286 228
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t151 : ((-50888667537/2000000000000 : ℚ) : ℝ) ≤ stT286 151 := by
  have hc : ((-62533/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50888667537/2000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-62533/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c152 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-402567/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6266743/10000000) (δ := 14457/1000000000) (ψ := 487099/1000000) 286 229
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t152 : ((-81641467409/1250000000000 : ℚ) : ℝ) ≤ stT286 152 := by
  have hc : ((-402617/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81641467409/1250000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-402617/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c153 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((100909/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -789101/5000000) (δ := 14457/1000000000) (ψ := 487099/1000000) 286 229
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t153 : ((40784988609/625000000000 : ℚ) : ℝ) ≤ stT286 153 := by
  have hc : ((201793/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40784988609/625000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((201793/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c154 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((41553/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3079809/10000000) (δ := 7173/500000000) (ψ := 487099/1000000) 286 229
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t154 : ((33474248791/1250000000000 : ℚ) : ℝ) ≤ stT286 154 := by
  have hc : ((83081/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33474248791/1250000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((83081/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c155 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-998287/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3853823/5000000) (δ := 14457/1000000000) (ψ := 487099/1000000) 286 229
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t155 : ((-40096220307/500000000000 : ℚ) : ℝ) ≤ stT286 155 := by
  have hc : ((-998387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40096220307/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-998387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c156 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((208369/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3402223/10000000) (δ := 14453/1000000000) (ψ := 487099/1000000) 286 230
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t156 : ((260544519/15625000000 : ℚ) : ℝ) ≤ stT286 156 := by
  have hc : ((208269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260544519/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((208269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c157 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((446553/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 291621/2500000) (δ := 14453/1000000000) (ψ := 487099/1000000) 286 230
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t157 : ((178173896629/2500000000000 : ℚ) : ℝ) ≤ stT286 157 := by
  have hc : ((446503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178173896629/2500000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((446503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c158 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-326549/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2853081/5000000) (δ := 14453/1000000000) (ψ := 487099/1000000) 286 230
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t158 : ((-129914223621/2500000000000 : ℚ) : ℝ) ≤ stT286 158 := by
  have hc : ((-326599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129914223621/2500000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-326599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c159 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-585497/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1372681/2500000) (δ := 14443/1000000000) (ψ := 487099/1000000) 286 231
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t159 : ((-116102218011/2500000000000 : ℚ) : ℝ) ≤ stT286 159 := by
  have hc : ((-585597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116102218011/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-585597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c160 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((114977/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25199/250000) (δ := 14443/1000000000) (ψ := 487099/1000000) 286 231
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t160 : ((181774739601/2500000000000 : ℚ) : ℝ) ≤ stT286 160 := by
  have hc : ((229929/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181774739601/2500000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((229929/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c161 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((190879/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 53857/156250) (δ := 359/25000000) (ψ := 487099/1000000) 286 231
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t161 : ((15035483769/1000000000000 : ℚ) : ℝ) ≤ stT286 161 := by
  have hc : ((190779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15035483769/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((190779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c162 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-31249/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1566767/2000000) (δ := 14467/1000000000) (ψ := 487099/1000000) 286 232
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t162 : ((-7857284259/100000000000 : ℚ) : ℝ) ≤ stT286 162 := by
  have hc : ((-250017/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7857284259/100000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-250017/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c163 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((49/250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3433797/10000000) (δ := 28/1953125) (ψ := 487099/1000000) 286 232
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t163 : ((76720317/5000000000 : ℚ) : ℝ) ≤ stT286 163 := by
  have hc : ((1959/10000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76720317/5000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((1959/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c164 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((465123/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 469643/5000000) (δ := 28/1953125) (ψ := 487099/1000000) 286 232
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t164 : ((90790155841/1250000000000 : ℚ) : ℝ) ≤ stT286 164 := by
  have hc : ((465073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90790155841/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((465073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c165 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-103429/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5285771/10000000) (δ := 28/1953125) (ψ := 487099/1000000) 286 232
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t165 : ((-80534943051/2000000000000 : ℚ) : ℝ) ≤ stT286 165 := by
  have hc : ((-103449/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80534943051/2000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-103449/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c166 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-382159/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1525487/2500000) (δ := 14429/1000000000) (ψ := 487099/1000000) 286 233
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t166 : ((-296651897559/5000000000000 : ℚ) : ℝ) ≤ stT286 166 := by
  have hc : ((-382209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-296651897559/5000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-382209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c167 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((749801/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -903793/5000000) (δ := 7187/500000000) (ψ := 487099/1000000) 286 233
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t167 : ((580135876923/10000000000000 : ℚ) : ℝ) ≤ stT286 167 := by
  have hc : ((749701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((580135876923/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((749701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c168 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((553351/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 492207/2000000) (δ := 14429/1000000000) (ψ := 487099/1000000) 286 233
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t168 : ((106710499629/2500000000000 : ℚ) : ℝ) ≤ stT286 168 := by
  have hc : ((553251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106710499629/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((553251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c169 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-89613/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6704417/10000000) (δ := 14429/1000000000) (ψ := 487099/1000000) 286 233
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t169 : ((-68940789913/1000000000000 : ℚ) : ℝ) ≤ stT286 169 := by
  have hc : ((-89623/100000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68940789913/1000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-89623/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c170 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-84151/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -239263/500000) (δ := 7241/500000000) (ψ := 487099/1000000) 286 234
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t170 : ((-807000573/31250000000 : ℚ) : ℝ) ≤ stT286 170 := by
  have hc : ((-5261/15625 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-807000573/31250000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-5261/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c171 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((24303/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -295857/5000000) (δ := 14321/1000000000) (ψ := 487099/1000000) 286 234
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t171 : ((37166108119/500000000000 : ℚ) : ℝ) ≤ stT286 171 := by
  have hc : ((48601/50000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37166108119/500000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((48601/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c172 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((139389/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 178869/500000) (δ := 7241/500000000) (ψ := 487099/1000000) 286 234
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t172 : ((26551687047/2500000000000 : ℚ) : ℝ) ≤ stT286 172 := by
  have hc : ((139289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26551687047/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((139289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c173 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-998613/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3861153/5000000) (δ := 14321/1000000000) (ψ := 487099/1000000) 286 234
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t173 : ((-379653755959/5000000000000 : ℚ) : ℝ) ≤ stT286 173 := by
  have hc : ((-998713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-379653755959/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-998713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c174 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((24949/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -966153/2500000) (δ := 7207/500000000) (ψ := 487099/1000000) 286 235
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t174 : ((9418988601/5000000000000 : ℚ) : ℝ) ≤ stT286 174 := by
  have hc : ((24849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9418988601/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((24849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c175 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((497833/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 232839/10000000) (δ := 14389/1000000000) (ψ := 487099/1000000) 286 235
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t175 : ((47036013453/625000000000 : ℚ) : ℝ) ≤ stT286 175 := by
  have hc : ((497783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47036013453/625000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((497783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c176 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-151383/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4306909/10000000) (δ := 14389/1000000000) (ψ := 487099/1000000) 286 235
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t176 : ((-114184704257/10000000000000 : ℚ) : ℝ) ≤ stT286 176 := by
  have hc : ((-151483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114184704257/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-151483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c177 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-979749/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7350007/10000000) (δ := 453/31250000) (ψ := 487099/1000000) 286 236
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t177 : ((-736500561303/10000000000000 : ℚ) : ℝ) ≤ stT286 177 := by
  have hc : ((-979849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-736500561303/10000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-979849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c178 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((239703/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41523/125000) (δ := 453/31250000) (ψ := 487099/1000000) 286 236
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t178 : ((179589876193/10000000000000 : ℚ) : ℝ) ≤ stT286 178 := by
  have hc : ((239603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179589876193/10000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((239603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c179 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((481413/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 170951/2500000) (δ := 14307/1000000000) (ψ := 487099/1000000) 286 236
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t179 : ((71957510781/1000000000000 : ℚ) : ℝ) ≤ stT286 179 := by
  have hc : ((481363/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71957510781/1000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((481363/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c180 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-145863/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4667069/10000000) (δ := 14307/1000000000) (ψ := 487099/1000000) 286 236
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t180 : ((-27189282507/1250000000000 : ℚ) : ℝ) ≤ stT286 180 := by
  have hc : ((-145913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27189282507/1250000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-145913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c181 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-190483/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7079651/10000000) (δ := 14403/1000000000) (ψ := 487099/1000000) 286 237
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t181 : ((-28319985477/400000000000 : ℚ) : ℝ) ≤ stT286 181 := by
  have hc : ((-190503/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28319985477/400000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-190503/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c182 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((154757/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3140287/10000000) (δ := 14403/1000000000) (ψ := 487099/1000000) 286 237
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t182 : ((114676409043/5000000000000 : ℚ) : ℝ) ≤ stT286 182 := by
  have hc : ((154707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114676409043/5000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((154707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c183 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((952021/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 155511/2000000) (δ := 9/625000) (ψ := 487099/1000000) 286 237
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t183 : ((703679993541/10000000000000 : ℚ) : ℝ) ≤ stT286 183 := by
  have hc : ((951921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((703679993541/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((951921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c184 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-18399/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4674019/10000000) (δ := 9/625000) (ψ := 487099/1000000) 286 237
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t184 : ((-5427413741/250000000000 : ℚ) : ℝ) ≤ stT286 184 := by
  have hc : ((-73621/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5427413741/250000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-73621/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c185 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-961561/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7158573/10000000) (δ := 14493/1000000000) (ψ := 487099/1000000) 286 238
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t185 : ((-141405518423/2000000000000 : ℚ) : ℝ) ≤ stT286 185 := by
  have hc : ((-961661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141405518423/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-961661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c186 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((246567/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3304151/10000000) (δ := 14493/1000000000) (ψ := 487099/1000000) 286 238
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t186 : ((36143646149/2000000000000 : ℚ) : ℝ) ≤ stT286 186 := by
  have hc : ((246467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36143646149/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((246467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c187 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((977639/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 529679/10000000) (δ := 14493/1000000000) (ψ := 487099/1000000) 286 238
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t187 : ((89355862451/1250000000000 : ℚ) : ℝ) ≤ stT286 187 := by
  have hc : ((977539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89355862451/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((977539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c188 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-2588/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4342989/10000000) (δ := 1431/100000000) (ψ := 487099/1000000) 286 238
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t188 : ((-1208724909/100000000000 : ℚ) : ℝ) ≤ stT286 188 := by
  have hc : ((-41433/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1208724909/100000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-41433/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c189 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-496819/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1892957/2500000) (δ := 7193/500000000) (ψ := 487099/1000000) 286 239
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t189 : ((-361419032517/5000000000000 : ℚ) : ℝ) ≤ stT286 189 := by
  have hc : ((-496869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-361419032517/5000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-496869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c190 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((10253/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3798773/10000000) (δ := 7193/500000000) (ψ := 487099/1000000) 286 239
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t190 : ((1855948977/500000000000 : ℚ) : ℝ) ≤ stT286 190 := by
  have hc : ((10233/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1855948977/500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((10233/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c191 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((199967/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11363/2500000) (δ := 7193/500000000) (ψ := 487099/1000000) 286 239
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t191 : ((72338225289/1000000000000 : ℚ) : ℝ) ≤ stT286 191 := by
  have hc : ((199947/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72338225289/1000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((199947/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c192 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((11921/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3688207/10000000) (δ := 14417/1000000000) (ψ := 487099/1000000) 286 239
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t192 : ((17188419279/2500000000000 : ℚ) : ℝ) ≤ stT286 192 := by
  have hc : ((23817/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17188419279/2500000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((23817/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c193 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-983737/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7402489/10000000) (δ := 14417/1000000000) (ψ := 487099/1000000) 286 239
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t193 : ((-88522701749/1250000000000 : ℚ) : ℝ) ≤ stT286 193 := by
  have hc : ((-983837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88522701749/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-983837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c194 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-134977/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -922071/2000000) (δ := 7239/500000000) (ψ := 487099/1000000) 286 240
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t194 : ((-96943849893/5000000000000 : ℚ) : ℝ) ≤ stT286 194 := by
  have hc : ((-135027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96943849893/5000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-135027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c195 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((465491/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -467127/5000000) (δ := 7239/500000000) (ψ := 487099/1000000) 286 240
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t195 : ((166654408137/2500000000000 : ℚ) : ℝ) ≤ stT286 195 := by
  have hc : ((465441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166654408137/2500000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((465441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c196 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((463179/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2723043/10000000) (δ := 573/40000000) (ψ := 487099/1000000) 286 240
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t196 : ((66154076703/2000000000000 : ℚ) : ℝ) ≤ stT286 196 := by
  have hc : ((463079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66154076703/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((463079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c197 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-413543/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6361749/10000000) (δ := 7239/500000000) (ψ := 487099/1000000) 286 240
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t197 : ((-294673018303/5000000000000 : ℚ) : ℝ) ≤ stT286 197 := by
  have hc : ((-413593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-294673018303/5000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-413593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c198 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-659073/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2862977/5000000) (δ := 451/31250000) (ψ := 487099/1000000) 286 241
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t198 : ((-46845447591/1000000000000 : ℚ) : ℝ) ≤ stT286 198 := by
  have hc : ((-659173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46845447591/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-659173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c199 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((330153/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2123927/10000000) (δ := 451/31250000) (ψ := 487099/1000000) 286 241
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t199 : ((234003744743/5000000000000 : ℚ) : ℝ) ≤ stT286 199 := by
  have hc : ((330103/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234003744743/5000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((330103/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c200 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((417131/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 146001/1000000) (δ := 14371/1000000000) (ψ := 487099/1000000) 286 241
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t200 : ((147460238793/2500000000000 : ℚ) : ℝ) ≤ stT286 200 := by
  have hc : ((417081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147460238793/2500000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((417081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c201 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-425633/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 157067/312500) (δ := 14371/1000000000) (ψ := 487099/1000000) 286 241
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t201 : ((-150144534309/5000000000000 : ℚ) : ℝ) ≤ stT286 201 := by
  have hc : ((-425733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-150144534309/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-425733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c202 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-479379/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7133489/10000000) (δ := 113/7812500) (ψ := 487099/1000000) 286 242
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t202 : ((-168662642771/2500000000000 : ℚ) : ℝ) ≤ stT286 202 := by
  have hc : ((-479429/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168662642771/2500000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-479429/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c203 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((129391/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -900651/2500000) (δ := 14339/1000000000) (ψ := 487099/1000000) 286 242
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t203 : ((45372219921/5000000000000 : ℚ) : ℝ) ≤ stT286 203 := by
  have hc : ((129291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45372219921/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((129291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c204 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((199873/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -44547/5000000) (δ := 14339/1000000000) (ψ := 487099/1000000) 286 242
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t204 : ((6996253971/100000000000 : ℚ) : ℝ) ≤ stT286 204 := by
  have hc : ((199853/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6996253971/100000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((199853/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c205 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((129/625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 425907/1250000) (δ := 14339/1000000000) (ψ := 487099/1000000) 286 242
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t205 : ((144086109/10000000000 : ℚ) : ℝ) ≤ stT286 205 := by
  have hc : ((2063/10000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144086109/10000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((2063/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c206 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-463031/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6886589/10000000) (δ := 14339/1000000000) (ψ := 487099/1000000) 286 242
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t206 : ((-161322138727/2500000000000 : ℚ) : ℝ) ≤ stT286 206 := by
  have hc : ((-463081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161322138727/2500000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-463081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c207 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-270981/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1071783/2000000) (δ := 7223/500000000) (ψ := 487099/1000000) 286 243
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t207 : ((-188379825519/5000000000000 : ℚ) : ℝ) ≤ stT286 207 := by
  have hc : ((-271031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188379825519/5000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-271031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c208 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((180303/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -478279/2500000) (δ := 14357/1000000000) (ψ := 487099/1000000) 286 243
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t208 : ((500001033/10000000000 : ℚ) : ℝ) ≤ stT286 208 := by
  have hc : ((90139/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((500001033/10000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((90139/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c209 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((821667/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1516167/10000000) (δ := 14357/1000000000) (ψ := 487099/1000000) 286 243
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t209 : ((284144697919/5000000000000 : ℚ) : ℝ) ≤ stT286 209 := by
  have hc : ((821567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((284144697919/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((821567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c210 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-390187/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4929077/10000000) (δ := 7223/500000000) (ψ := 487099/1000000) 286 243
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t210 : ((-134661894471/5000000000000 : ℚ) : ℝ) ≤ stT286 210 := by
  have hc : ((-390287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134661894471/5000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-390287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c211 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-982247/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115347/156250) (δ := 289/20000000) (ψ := 487099/1000000) 286 244
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t211 : ((-676276162863/10000000000000 : ℚ) : ℝ) ≤ stT286 211 := by
  have hc : ((-982347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-676276162863/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-982347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c212 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-14923/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -250101/625000) (δ := 14353/1000000000) (ψ := 487099/1000000) 286 244
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t212 : ((-10283501319/5000000000000 : ℚ) : ℝ) ≤ stT286 212 := by
  have hc : ((-14973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10283501319/5000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-14973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c213 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((241931/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -318449/5000000) (δ := 289/20000000) (ψ := 487099/1000000) 286 244
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t213 : ((20718886041/312500000000 : ℚ) : ℝ) ≤ stT286 213 := by
  have hc : ((120953/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20718886041/312500000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((120953/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c214 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((467057/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2712091/10000000) (δ := 14353/1000000000) (ψ := 487099/1000000) 286 244
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t214 : ((63840960169/2000000000000 : ℚ) : ℝ) ≤ stT286 214 := by
  have hc : ((466957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63840960169/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((466957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c215 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-749543/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6045421/10000000) (δ := 14353/1000000000) (ψ := 487099/1000000) 286 244
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t215 : ((-102250555557/2000000000000 : ℚ) : ℝ) ≤ stT286 215 := by
  have hc : ((-749643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102250555557/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-749643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c216 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-102903/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -396541/625000) (δ := 723/50000000) (ψ := 487099/1000000) 286 245
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t216 : ((-70025147017/1250000000000 : ℚ) : ℝ) ≤ stT286 216 := by
  have hc : ((-205831/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70025147017/1250000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-205831/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c217 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((69319/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3042143/10000000) (δ := 14343/1000000000) (ψ := 487099/1000000) 286 245
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t217 : ((11760802589/500000000000 : ℚ) : ℝ) ≤ stT286 217 := by
  have hc : ((69299/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11760802589/500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((69299/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c218 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((497597/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 245213/10000000) (δ := 723/50000000) (ψ := 487099/1000000) 286 245
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t218 : ((67396223979/1000000000000 : ℚ) : ℝ) ≤ stT286 218 := by
  have hc : ((497547/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67396223979/1000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((497547/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c219 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((40761/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3517553/10000000) (δ := 14343/1000000000) (ψ := 487099/1000000) 286 245
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t219 : ((860213201/78125000000 : ℚ) : ℝ) ≤ stT286 219 := by
  have hc : ((2546/15625 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((860213201/78125000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((2546/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c220 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-227073/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 135499/200000) (δ := 14343/1000000000) (ψ := 487099/1000000) 286 245
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t220 : ((-382773679/6250000000 : ℚ) : ℝ) ≤ stT286 220 := by
  have hc : ((-113549/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-382773679/6250000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-113549/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c221 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-324147/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1138069/2000000) (δ := 449/31250000) (ψ := 487099/1000000) 286 246
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t221 : ((-218078568581/5000000000000 : ℚ) : ℝ) ≤ stT286 221 := by
  have hc : ((-324197/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218078568581/5000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-324197/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c222 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((276447/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1231203/5000000) (δ := 449/31250000) (ψ := 487099/1000000) 286 246
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t222 : ((46376376233/1250000000000 : ℚ) : ℝ) ≤ stT286 222 := by
  have hc : ((276397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46376376233/1250000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((276397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c223 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((119401/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75109/1000000) (δ := 449/31250000) (ψ := 487099/1000000) 286 246
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t223 : ((159896779273/2500000000000 : ℚ) : ℝ) ≤ stT286 223 := by
  have hc : ((238777/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159896779273/2500000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((238777/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c224 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-9289/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1975107/5000000) (δ := 2887/200000000) (ψ := 487099/1000000) 286 246
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t224 : ((-3136648953/5000000000000 : ℚ) : ℝ) ≤ stT286 224 := by
  have hc : ((-9389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3136648953/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-9389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c225 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-479471/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 713511/1000000) (δ := 2887/200000000) (ψ := 487099/1000000) 286 246
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t225 : ((-319680826507/5000000000000 : ℚ) : ℝ) ≤ stT286 225 := by
  have hc : ((-479521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-319680826507/5000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-479521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c226 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-278207/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -108043/200000) (δ := 3591/125000000) (ψ := 487099/1000000) 286 247
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t226 : ((-185094052087/5000000000000 : ℚ) : ℝ) ≤ stT286 226 := by
  have hc : ((-278257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185094052087/5000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-278257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c227 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((311527/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2245389/10000000) (δ := 1791/125000000) (ψ := 487099/1000000) 286 247
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t227 : ((206734448871/5000000000000 : ℚ) : ℝ) ≤ stT286 227 := by
  have hc : ((311477/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((206734448871/5000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((311477/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c228 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((468127/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 179493/2000000) (δ := 1791/125000000) (ψ := 487099/1000000) 286 247
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t228 : ((154995741241/2500000000000 : ℚ) : ℝ) ≤ stT286 228 := by
  have hc : ((468077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154995741241/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((468077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c229 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-3983/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4026591/10000000) (δ := 1791/125000000) (ψ := 487099/1000000) 286 247
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t229 : ((-2638650267/1000000000000 : ℚ) : ℝ) ≤ stT286 229 := by
  have hc : ((-3993/100000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2638650267/1000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-3993/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c230 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-959727/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7142061/10000000) (δ := 579/40000000) (ψ := 487099/1000000) 286 247
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t230 : ((-632891687087/10000000000000 : ℚ) : ℝ) ≤ stT286 230 := by
  have hc : ((-959827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-632891687087/10000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-959827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c231 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-576781/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5463947/10000000) (δ := 14421/1000000000) (ψ := 487099/1000000) 286 248
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t231 : ((-11861250241/312500000000 : ℚ) : ℝ) ≤ stT286 231 := by
  have hc : ((-576881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11861250241/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-576881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c232 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((290771/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2375433/10000000) (δ := 14421/1000000000) (ψ := 487099/1000000) 286 248
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t232 : ((47716909893/1250000000000 : ℚ) : ℝ) ≤ stT286 232 := by
  have hc : ((290721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47716909893/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((290721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c233 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((60067/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 349927/5000000) (δ := 7191/500000000) (ψ := 487099/1000000) 286 248
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t233 : ((157388234403/2500000000000 : ℚ) : ℝ) ≤ stT286 233 := by
  have hc : ((240243/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157388234403/2500000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((240243/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c234 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((13191/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58781/156250) (δ := 14421/1000000000) (ψ := 487099/1000000) 286 248
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t234 : ((215253653/50000000000 : ℚ) : ℝ) ≤ stT286 234 := by
  have hc : ((13171/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215253653/50000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((13171/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c235 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-182847/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 681103/1000000) (δ := 14421/1000000000) (ψ := 487099/1000000) 286 248
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t235 : ((-119289447243/2000000000000 : ℚ) : ℝ) ≤ stT286 235 := by
  have hc : ((-182867/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119289447243/2000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-182867/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c236 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-698669/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1465207/2500000) (δ := 14489/1000000000) (ψ := 487099/1000000) 286 249
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t236 : ((-90972037341/2000000000000 : ℚ) : ℝ) ≤ stT286 236 := by
  have hc : ((-698769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90972037341/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-698769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c237 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((211049/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1418797/5000000) (δ := 7157/500000000) (ψ := 487099/1000000) 286 249
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t237 : ((137058409431/5000000000000 : ℚ) : ℝ) ≤ stT286 237 := by
  have hc : ((210999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137058409431/5000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((210999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c238 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((997609/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 86457/5000000) (δ := 14489/1000000000) (ψ := 487099/1000000) 286 249
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t238 : ((646588326327/10000000000000 : ℚ) : ℝ) ≤ stT286 238 := by
  have hc : ((997509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((646588326327/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((997509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c239 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((297871/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3170837/10000000) (δ := 7157/500000000) (ψ := 487099/1000000) 286 249
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t239 : ((96305990133/5000000000000 : ℚ) : ℝ) ≤ stT286 239 := by
  have hc : ((297771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96305990133/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((297771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c240 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-389071/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 769531/1250000) (δ := 7157/500000000) (ψ := 487099/1000000) 286 249
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t240 : ((-125588413629/2500000000000 : ℚ) : ℝ) ≤ stT286 240 := by
  have hc : ((-389121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125588413629/2500000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-389121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c241 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-436349/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1315749/2000000) (δ := 3599/250000000) (ψ := 487099/1000000) 286 250
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t241 : ((-281109470643/5000000000000 : ℚ) : ℝ) ≤ stT286 241 := by
  have hc : ((-436399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-281109470643/5000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-436399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c242 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((123253/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3618073/10000000) (δ := 3599/250000000) (ψ := 487099/1000000) 286 250
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t242 : ((9895713009/1250000000000 : ℚ) : ℝ) ≤ stT286 242 := by
  have hc : ((123153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9895713009/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((123153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c243 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((482171/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -167407/2500000) (δ := 14407/1000000000) (ψ := 487099/1000000) 286 250
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t243 : ((618561243/10000000000 : ℚ) : ℝ) ≤ stT286 243 := by
  have hc : ((482121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((618561243/10000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((482121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c244 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((616353/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1133367/5000000) (δ := 14407/1000000000) (ψ := 487099/1000000) 286 250
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t244 : ((49314413819/1250000000000 : ℚ) : ℝ) ≤ stT286 244 := by
  have hc : ((616253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49314413819/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((616253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c245 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-484353/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5191049/10000000) (δ := 7199/250000000) (ψ := 487099/1000000) 286 250
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t245 : ((-309505879281/10000000000000 : ℚ) : ℝ) ≤ stT286 245 := by
  have hc : ((-484453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-309505879281/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-484453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c246 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-62189/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -760447/1000000) (δ := 14499/1000000000) (ψ := 487099/1000000) 286 251
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t246 : ((-158617043637/2500000000000 : ℚ) : ℝ) ≤ stT286 246 := by
  have hc : ((-248781/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158617043637/2500000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-248781/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c247 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-30577/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2351929/5000000) (δ := 14499/1000000000) (ψ := 487099/1000000) 286 251
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t247 : ((-3892409859/200000000000 : ℚ) : ℝ) ≤ stT286 247 := by
  have hc : ((-30587/100000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3892409859/200000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-30587/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c248 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((747843/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -453743/2500000) (δ := 14499/1000000000) (ψ := 487099/1000000) 286 251
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t248 : ((94963361/2000000000 : ℚ) : ℝ) ≤ stT286 248 := by
  have hc : ((747743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94963361/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((747743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c249 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((455539/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 53113/500000) (δ := 447/31250000) (ψ := 487099/1000000) 286 251
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t249 : ((72163577759/1250000000000 : ℚ) : ℝ) ≤ stT286 249 := by
  have hc : ((455489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72163577759/1250000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((455489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c250 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-53/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3928051/10000000) (δ := 14499/1000000000) (ψ := 487099/1000000) 286 251
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t250 : ((-10356467/312500000000 : ℚ) : ℝ) ≤ stT286 250 := by
  have hc : ((-131/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10356467/312500000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-131/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c251 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-909523/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6782331/10000000) (δ := 14499/1000000000) (ψ := 487099/1000000) 286 251
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t251 : ((-114829897897/2000000000000 : ℚ) : ℝ) ≤ stT286 251 := by
  have hc : ((-909623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).2
  have h0 : (0:ℝ) ≤ ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114829897897/2000000000000 : ℚ) : ℝ)
      = ((126239/2000000 : ℚ) : ℝ) * ((-909623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c252 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-94917/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -38017/62500) (δ := 14411/1000000000) (ψ := 487099/1000000) 286 252
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t252 : ((-119599968319/2500000000000 : ℚ) : ℝ) ≤ stT286 252 := by
  have hc : ((-189859/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).2
  have h0 : (0:ℝ) ≤ ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119599968319/2500000000000 : ℚ) : ℝ)
      = ((629941/10000000 : ℚ) : ℝ) * ((-189859/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c253 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((2671/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1625517/5000000) (δ := 14411/1000000000) (ψ := 487099/1000000) 286 252
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t253 : ((83930649/5000000000 : ℚ) : ℝ) ≤ stT286 253 := by
  have hc : ((267/1000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).1
  have hw2 : ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((314347/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83930649/5000000000 : ℚ) : ℝ)
      = ((314347/5000000 : ℚ) : ℝ) * ((267/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c254 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((98521/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -215251/5000000) (δ := 14411/1000000000) (ψ := 487099/1000000) 286 252
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t254 : ((12362243901/200000000000 : ℚ) : ℝ) ≤ stT286 254 := by
  have hc : ((98511/100000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).1
  have hw2 : ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((125491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12362243901/200000000000 : ℚ) : ℝ)
      = ((125491/2000000 : ℚ) : ℝ) * ((98511/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c255 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((290199/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2378947/10000000) (δ := 1799/125000000) (ψ := 487099/1000000) 286 252
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t255 : ((11356141711/312500000000 : ℚ) : ℝ) ≤ stT286 255 := by
  have hc : ((290149/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).1
  have hw2 : ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39139/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11356141711/312500000000 : ℚ) : ℝ)
      = ((39139/625000 : ℚ) : ℝ) * ((290149/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c256 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-119891/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2588693/5000000) (δ := 14411/1000000000) (ψ := 487099/1000000) 286 252
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t256 : ((-18736904979/625000000000 : ℚ) : ℝ) ≤ stT286 256 := by
  have hc : ((-29979/62500 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).2
  have h0 : (0:ℝ) ≤ ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18736904979/625000000000 : ℚ) : ℝ)
      = ((625001/10000000 : ℚ) : ℝ) * ((-29979/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c257 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-124877/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7743079/10000000) (δ := 2897/200000000) (ψ := 487099/1000000) 286 253
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t257 : ((-155807893957/2500000000000 : ℚ) : ℝ) ≤ stT286 257 := by
  have hc : ((-249779/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).2
  have h0 : (0:ℝ) ≤ ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155807893957/2500000000000 : ℚ) : ℝ)
      = ((623783/10000000 : ℚ) : ℝ) * ((-249779/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c258 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-10097/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -620797/1250000) (δ := 7159/500000000) (ψ := 487099/1000000) 286 253
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t258 : ((-12575352027/500000000000 : ℚ) : ℝ) ≤ stT286 258 := by
  have hc : ((-20199/50000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).2
  have h0 : (0:ℝ) ≤ ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12575352027/500000000000 : ℚ) : ℝ)
      = ((622573/10000000 : ℚ) : ℝ) * ((-20199/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c259 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((159257/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2200399/10000000) (δ := 2897/200000000) (ψ := 487099/1000000) 286 253
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t259 : ((193245759/4882812500 : ℚ) : ℝ) ≤ stT286 259 := by
  have hc : ((9952/15625 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).1
  have hw2 : ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((621369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193245759/4882812500 : ℚ) : ℝ)
      = ((621369/10000000 : ℚ) : ℝ) * ((9952/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c260 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((487733/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 22197/400000) (δ := 2897/200000000) (ψ := 487099/1000000) 286 253
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t260 : ((302447829159/5000000000000 : ℚ) : ℝ) ≤ stT286 260 := by
  have hc : ((487683/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).1
  have hw2 : ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((620173/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((302447829159/5000000000000 : ℚ) : ℝ)
      = ((620173/10000000 : ℚ) : ℝ) * ((487683/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c261 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((15519/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3299667/10000000) (δ := 2897/200000000) (ψ := 487099/1000000) 286 253
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t261 : ((4801072023/312500000000 : ℚ) : ℝ) ≤ stT286 261 := by
  have hc : ((62051/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).1
  have hw2 : ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((77373/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4801072023/312500000000 : ℚ) : ℝ)
      = ((77373/1250000 : ℚ) : ℝ) * ((62051/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c262 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-149297/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6033899/10000000) (δ := 21459/500000000) (ψ := 487099/1000000) 286 253
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t262 : ((-92248490551/2000000000000 : ℚ) : ℝ) ≤ stT286 262 := by
  have hc : ((-149317/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92248490551/2000000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-149317/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c263 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-935373/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54299/78125) (δ := 7189/500000000) (ψ := 487099/1000000) 286 254
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t263 : ((-576837909571/10000000000000 : ℚ) : ℝ) ≤ stT286 263 := by
  have hc : ((-935473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).2
  have h0 : (0:ℝ) ≤ ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-576837909571/10000000000000 : ℚ) : ℝ)
      = ((616627/10000000 : ℚ) : ℝ) * ((-935473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c264 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-123597/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -169471/400000) (δ := 1721/40000000) (ψ := 487099/1000000) 286 254
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t264 : ((-38065154113/5000000000000 : ℚ) : ℝ) ≤ stT286 264 := by
  have hc : ((-123697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).2
  have h0 : (0:ℝ) ≤ ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38065154113/5000000000000 : ℚ) : ℝ)
      = ((307729/5000000 : ℚ) : ℝ) * ((-123697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c265 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((408839/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -61343/400000) (δ := 7189/500000000) (ψ := 487099/1000000) 286 254
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t265 : ((50223407751/1000000000000 : ℚ) : ℝ) ≤ stT286 265 := by
  have hc : ((408789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50223407751/1000000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((408789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c266 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((223591/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1159473/10000000) (δ := 577/40000000) (ψ := 487099/1000000) 286 254
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t266 : ((68538516837/1250000000000 : ℚ) : ℝ) ≤ stT286 266 := by
  have hc : ((111783/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).1
  have hw2 : ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((613139/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68538516837/1250000000000 : ℚ) : ℝ)
      = ((613139/10000000 : ℚ) : ℝ) * ((111783/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c267 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((33843/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3842367/10000000) (δ := 7189/500000000) (ψ := 487099/1000000) 286 254
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t267 : ((2065037857/1000000000000 : ℚ) : ℝ) ≤ stT286 267 := by
  have hc : ((33743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).1
  have hw2 : ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61199/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2065037857/1000000000000 : ℚ) : ℝ)
      = ((61199/1000000 : ℚ) : ℝ) * ((33743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c268 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-430009/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1628813/2500000) (δ := 577/40000000) (ψ := 487099/1000000) 286 254
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t268 : ((-8209396251/156250000000 : ℚ) : ℝ) ≤ stT286 268 := by
  have hc : ((-430059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8209396251/156250000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-430059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c269 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-431483/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3264883/5000000) (δ := 14471/1000000000) (ψ := 487099/1000000) 286 255
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t269 : ((-263110416963/5000000000000 : ℚ) : ℝ) ≤ stT286 269 := by
  have hc : ((-431533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).2
  have h0 : (0:ℝ) ≤ ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-263110416963/5000000000000 : ℚ) : ℝ)
      = ((609711/10000000 : ℚ) : ℝ) * ((-431533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c270 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((503/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3876687/10000000) (δ := 14471/1000000000) (ψ := 487099/1000000) 286 255
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t270 : ((30459429/25000000000 : ℚ) : ℝ) ≤ stT286 270 := by
  have hc : ((1001/50000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30459429/25000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((1001/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c271 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((440373/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1233403/10000000) (δ := 3583/250000000) (ψ := 487099/1000000) 286 255
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t271 : ((8358651509/156250000000 : ℚ) : ℝ) ≤ stT286 271 := by
  have hc : ((440323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8358651509/156250000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((440323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c272 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((847237/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 280017/2000000) (δ := 3583/250000000) (ψ := 487099/1000000) 286 255
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t272 : ((513652201443/10000000000000 : ℚ) : ℝ) ≤ stT286 272 := by
  have hc : ((847137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).1
  have hw2 : ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((513652201443/10000000000000 : ℚ) : ℝ)
      = ((606339/10000000 : ℚ) : ℝ) * ((847137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c273 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-19381/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50299/125000) (δ := 14471/1000000000) (ψ := 487099/1000000) 286 255
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t273 : ((-2940046317/1250000000000 : ℚ) : ℝ) ≤ stT286 273 := by
  have hc : ((-19431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2940046317/1250000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-19431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c274 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-884071/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3319123/5000000) (δ := 14471/1000000000) (ψ := 487099/1000000) 286 255
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t274 : ((-534148037033/10000000000000 : ℚ) : ℝ) ≤ stT286 274 := by
  have hc : ((-884171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-534148037033/10000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-884171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c275 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-849597/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6465043/10000000) (δ := 14439/1000000000) (ψ := 487099/1000000) 286 256
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t275 : ((-512386834031/10000000000000 : ℚ) : ℝ) ≤ stT286 275 := by
  have hc : ((-849697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512386834031/10000000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-849697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c276 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((229/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -483717/1250000) (δ := 14439/1000000000) (ψ := 487099/1000000) 286 256
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t276 : ((34309953/25000000000 : ℚ) : ℝ) ≤ stT286 276 := by
  have hc : ((57/2500 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34309953/25000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((57/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c277 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((435511/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -320949/2500000) (δ := 3591/250000000) (ψ := 487099/1000000) 286 256
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t277 : ((261642822701/5000000000000 : ℚ) : ℝ) ≤ stT286 277 := by
  have hc : ((435461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261642822701/5000000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((435461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c278 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((869251/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 646389/5000000) (δ := 3591/250000000) (ψ := 487099/1000000) 286 256
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t278 : ((6516025047/125000000000 : ℚ) : ℝ) ≤ stT286 278 := by
  have hc : ((869151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6516025047/125000000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((869151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c279 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((2677/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3860057/10000000) (δ := 3591/250000000) (ψ := 487099/1000000) 286 256
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t279 : ((399172557/250000000000 : ℚ) : ℝ) ≤ stT286 279 := by
  have hc : ((2667/100000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).1
  have hw2 : ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149671/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((399172557/250000000000 : ℚ) : ℝ)
      = ((149671/2500000 : ℚ) : ℝ) * ((2667/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c280 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-419789/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 401141/625000) (δ := 14439/1000000000) (ψ := 487099/1000000) 286 256
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t280 : ((-50180416797/1000000000000 : ℚ) : ℝ) ≤ stT286 280 := by
  have hc : ((-419839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50180416797/1000000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-419839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c281 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-451241/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6740733/10000000) (δ := 1807/125000000) (ψ := 487099/1000000) 286 257
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t281 : ((-5384352921/100000000000 : ℚ) : ℝ) ≤ stT286 281 := by
  have hc : ((-451291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5384352921/100000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-451291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c282 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-27323/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4200767/10000000) (δ := 1807/125000000) (ψ := 487099/1000000) 286 257
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t282 : ((-1017844701/156250000000 : ℚ) : ℝ) ≤ stT286 282 := by
  have hc : ((-6837/62500 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).2
  have h0 : (0:ℝ) ≤ ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1017844701/156250000000 : ℚ) : ℝ)
      = ((148873/2500000 : ℚ) : ℝ) * ((-6837/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c283 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((785109/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -166981/1000000) (δ := 1807/125000000) (ψ := 487099/1000000) 286 257
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t283 : ((233319589971/5000000000000 : ℚ) : ℝ) ≤ stT286 283 := by
  have hc : ((785009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233319589971/5000000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((785009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c284 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((18849/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 852281/10000000) (δ := 1807/125000000) (ψ := 487099/1000000) 286 257
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t284 : ((1118362133/20000000000 : ℚ) : ℝ) ≤ stT286 284 := by
  have hc : ((18847/20000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1118362133/20000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((18847/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c285 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((111369/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 673087/2000000) (δ := 14347/1000000000) (ψ := 487099/1000000) 286 257
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t285 : ((16484896753/1250000000000 : ℚ) : ℝ) ≤ stT286 285 := by
  have hc : ((111319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).1
  have hw2 : ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((148087/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16484896753/1250000000000 : ℚ) : ℝ)
      = ((148087/2500000 : ℚ) : ℝ) * ((111319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c286 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-561/800 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1173973/2000000) (δ := 1807/125000000) (ψ := 487099/1000000) 286 257
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t286 : ((-8294347451/200000000000 : ℚ) : ℝ) ≤ stT286 286 := by
  have hc : ((-14027/20000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8294347451/200000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-14027/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c287 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-979141/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3671231/5000000) (δ := 14349/1000000000) (ψ := 487099/1000000) 286 258
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t287 : ((-289014167981/5000000000000 : ℚ) : ℝ) ≤ stT286 287 := by
  have hc : ((-979241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-289014167981/5000000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-979241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c288 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-181471/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4855549/10000000) (δ := 14349/1000000000) (ψ := 487099/1000000) 286 258
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t288 : ((-13370292297/625000000000 : ℚ) : ℝ) ≤ stT286 288 := by
  have hc : ((-181521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).2
  have h0 : (0:ℝ) ≤ ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13370292297/625000000000 : ℚ) : ℝ)
      = ((73657/1250000 : ℚ) : ℝ) * ((-181521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c289 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((290481/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18572/78125) (δ := 14349/1000000000) (ψ := 487099/1000000) 286 258
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t289 : ((34168335857/1000000000000 : ℚ) : ℝ) ≤ stT286 289 := by
  have hc : ((290431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34168335857/1000000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((290431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c290 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((499657/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 92609/10000000) (δ := 7227/500000000) (ψ := 487099/1000000) 286 258
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t290 : ((14668961127/250000000000 : ℚ) : ℝ) ≤ stT286 290 := by
  have hc : ((499607/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14668961127/250000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((499607/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c291 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((130513/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2553853/10000000) (δ := 14349/1000000000) (ψ := 487099/1000000) 286 258
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t291 : ((956167131/31250000000 : ℚ) : ℝ) ≤ stT286 291 := by
  have hc : ((16311/31250 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((956167131/31250000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((16311/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c292 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-209297/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1251683/2500000) (δ := 14349/1000000000) (ψ := 487099/1000000) 286 258
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t292 : ((-61255560241/2500000000000 : ℚ) : ℝ) ≤ stT286 292 := by
  have hc : ((-209347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).2
  have h0 : (0:ℝ) ≤ ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61255560241/2500000000000 : ℚ) : ℝ)
      = ((292603/5000000 : ℚ) : ℝ) * ((-209347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c293 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-123381/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3725587/5000000) (δ := 14349/1000000000) (ψ := 487099/1000000) 286 258
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t293 : ((-144174692909/2500000000000 : ℚ) : ℝ) ≤ stT286 293 := by
  have hc : ((-246787/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).2
  have h0 : (0:ℝ) ≤ ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144174692909/2500000000000 : ℚ) : ℝ)
      = ((584207/10000000 : ℚ) : ℝ) * ((-246787/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c294 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-687099/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5820713/10000000) (δ := 7221/500000000) (ψ := 487099/1000000) 286 259
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t294 : ((-100195675797/2500000000000 : ℚ) : ℝ) ≤ stT286 294 := by
  have hc : ((-687199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100195675797/2500000000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-687199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c295 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((212031/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3392859/10000000) (δ := 7221/500000000) (ψ := 487099/1000000) 286 259
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t295 : ((61695445341/5000000000000 : ℚ) : ℝ) ≤ stT286 295 := by
  have hc : ((211931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).1
  have hw2 : ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((291111/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61695445341/5000000000000 : ℚ) : ℝ)
      = ((291111/5000000 : ℚ) : ℝ) * ((211931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c296 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((462589/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -973227/10000000) (δ := 14361/1000000000) (ψ := 487099/1000000) 286 259
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t296 : ((134422621641/2500000000000 : ℚ) : ℝ) ≤ stT286 296 := by
  have hc : ((462539/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).1
  have hw2 : ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134422621641/2500000000000 : ℚ) : ℝ)
      = ((290619/5000000 : ℚ) : ℝ) * ((462539/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c297 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((209757/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1438253/10000000) (δ := 7221/500000000) (ψ := 487099/1000000) 286 259
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t297 : ((15212333857/312500000000 : ℚ) : ℝ) ≤ stT286 297 := by
  have hc : ((52433/62500 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).1
  have hw2 : ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290129/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15212333857/312500000000 : ℚ) : ℝ)
      = ((290129/5000000 : ℚ) : ℝ) * ((52433/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c298 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((8539/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3841583/10000000) (δ := 14361/1000000000) (ψ := 487099/1000000) 286 259
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t298 : ((616502997/312500000000 : ℚ) : ℝ) ≤ stT286 298 := by
  have hc : ((4257/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((616502997/312500000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((4257/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c299 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-398999/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 779613/1250000) (δ := 7221/500000000) (ψ := 487099/1000000) 286 259
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t299 : ((-46155204487/1000000000000 : ℚ) : ℝ) ≤ stT286 299 := by
  have hc : ((-399049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).2
  have h0 : (0:ℝ) ≤ ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46155204487/1000000000000 : ℚ) : ℝ)
      = ((115663/2000000 : ℚ) : ℝ) * ((-399049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c300 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-952913/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1416749/2000000) (δ := 3617/250000000) (ψ := 487099/1000000) 286 260
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t300 : ((-550223008563/10000000000000 : ℚ) : ℝ) ≤ stT286 300 := by
  have hc : ((-953013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).2
  have h0 : (0:ℝ) ≤ ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-550223008563/10000000000000 : ℚ) : ℝ)
      = ((577351/10000000 : ℚ) : ℝ) * ((-953013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c301 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-76491/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -294023/625000) (δ := 3617/250000000) (ψ := 487099/1000000) 286 260
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t301 : ((-11025783439/625000000000 : ℚ) : ℝ) ≤ stT286 301 := by
  have hc : ((-19129/62500 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).2
  have h0 : (0:ℝ) ≤ ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11025783439/625000000000 : ℚ) : ℝ)
      = ((576391/10000000 : ℚ) : ℝ) * ((-19129/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c302 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((37207/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -291607/1250000) (δ := 3617/250000000) (ψ := 487099/1000000) 286 260
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t302 : ((17125290861/500000000000 : ℚ) : ℝ) ≤ stT286 302 := by
  have hc : ((148803/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).1
  have hw2 : ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((115087/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17125290861/500000000000 : ℚ) : ℝ)
      = ((115087/2000000 : ℚ) : ℝ) * ((148803/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c303 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((249981/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30791/10000000) (δ := 3617/250000000) (ψ := 487099/1000000) 286 260
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t303 : ((8974732669/156250000000 : ℚ) : ℝ) ≤ stT286 303 := by
  have hc : ((62489/62500 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).1
  have hw2 : ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143621/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8974732669/156250000000 : ℚ) : ℝ)
      = ((143621/2500000 : ℚ) : ℝ) * ((62489/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c304 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((18059/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 596661/2500000) (δ := 2867/200000000) (ψ := 487099/1000000) 286 260
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t304 : ((82845987933/2500000000000 : ℚ) : ℝ) ≤ stT286 304 := by
  have hc : ((144447/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).1
  have hw2 : ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82845987933/2500000000000 : ℚ) : ℝ)
      = ((573539/10000000 : ℚ) : ℝ) * ((144447/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c305 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-158747/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 295919/625000) (δ := 2867/200000000) (ψ := 487099/1000000) 286 260
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t305 : ((-90927003403/5000000000000 : ℚ) : ℝ) ≤ stT286 305 := by
  have hc : ((-158797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).2
  have h0 : (0:ℝ) ≤ ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90927003403/5000000000000 : ℚ) : ℝ)
      = ((572599/10000000 : ℚ) : ℝ) * ((-158797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c306 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-951869/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1415037/2000000) (δ := 2867/200000000) (ψ := 487099/1000000) 286 260
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t306 : ((-272102251239/5000000000000 : ℚ) : ℝ) ≤ stT286 306 := by
  have hc : ((-951969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).2
  have h0 : (0:ℝ) ≤ ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-272102251239/5000000000000 : ℚ) : ℝ)
      = ((285831/5000000 : ℚ) : ℝ) * ((-951969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c307 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-203239/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6300019/10000000) (δ := 23/1600000) (ψ := 487099/1000000) 286 261
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t307 : ((-226580207/4882812500 : ℚ) : ℝ) ≤ stT286 307 := by
  have hc : ((-12704/15625 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).2
  have h0 : (0:ℝ) ≤ ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-226580207/4882812500 : ℚ) : ℝ)
      = ((570731/10000000 : ℚ) : ℝ) * ((-12704/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c308 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-9569/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3974839/10000000) (δ := 23/1600000) (ψ := 487099/1000000) 286 261
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t308 : ((-5480935057/5000000000000 : ℚ) : ℝ) ≤ stT286 308 := by
  have hc : ((-9619/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).2
  have h0 : (0:ℝ) ≤ ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5480935057/5000000000000 : ℚ) : ℝ)
      = ((569803/10000000 : ℚ) : ℝ) * ((-9619/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c309 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((788231/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1657167/10000000) (δ := 3607/250000000) (ψ := 487099/1000000) 286 261
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t309 : ((5604399541/125000000000 : ℚ) : ℝ) ≤ stT286 309 := by
  have hc : ((788131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5604399541/125000000000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((788131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c310 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((966081/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 326499/5000000) (δ := 3607/250000000) (ψ := 487099/1000000) 286 261
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t310 : ((548639534741/10000000000000 : ℚ) : ℝ) ≤ stT286 310 := by
  have hc : ((965981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).1
  have hw2 : ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567961/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((548639534741/10000000000000 : ℚ) : ℝ)
      = ((567961/10000000 : ℚ) : ℝ) * ((965981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c311 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((378779/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2955799/10000000) (δ := 23/1600000) (ψ := 487099/1000000) 286 261
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t311 : ((214728790913/10000000000000 : ℚ) : ℝ) ≤ stT286 311 := by
  have hc : ((378679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).1
  have hw2 : ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((214728790913/10000000000000 : ℚ) : ℝ)
      = ((567047/10000000 : ℚ) : ℝ) * ((378679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c312 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-505223/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1312773/2500000) (δ := 23/1600000) (ψ := 487099/1000000) 286 261
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t312 : ((-286083057897/10000000000000 : ℚ) : ℝ) ≤ stT286 312 := by
  have hc : ((-505323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286083057897/10000000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-505323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c313 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-496039/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1884773/2500000) (δ := 23/1600000) (ψ := 487099/1000000) 286 261
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t313 : ((-140203184913/2500000000000 : ℚ) : ℝ) ≤ stT286 313 := by
  have hc : ((-496089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140203184913/2500000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-496089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c314 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-14129/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1472041/2500000) (δ := 14483/1000000000) (ψ := 487099/1000000) 286 262
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t314 : ((-7974589623/200000000000 : ℚ) : ℝ) ≤ stT286 314 := by
  have hc : ((-14131/20000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).2
  have h0 : (0:ℝ) ≤ ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7974589623/200000000000 : ℚ) : ℝ)
      = ((564333/10000000 : ℚ) : ℝ) * ((-14131/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c315 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((623/5000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3614679/10000000) (δ := 179/12500000) (ψ := 487099/1000000) 286 262
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t315 : ((35073891/5000000000 : ℚ) : ℝ) ≤ stT286 315 := by
  have hc : ((249/2000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35073891/5000000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((249/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c316 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((429017/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -269683/2000000) (δ := 179/12500000) (ψ := 487099/1000000) 286 262
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t316 : ((241312383081/5000000000000 : ℚ) : ℝ) ≤ stT286 316 := by
  have hc : ((428967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((241312383081/5000000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((428967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c317 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((934391/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 227657/2500000) (δ := 14483/1000000000) (ψ := 487099/1000000) 286 262
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t317 : ((104949842321/2000000000000 : ℚ) : ℝ) ≤ stT286 317 := by
  have hc : ((934291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).1
  have hw2 : ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((112331/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104949842321/2000000000000 : ℚ) : ℝ)
      = ((112331/2000000 : ℚ) : ℝ) * ((934291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c318 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((150509/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 98831/312500) (δ := 14483/1000000000) (ψ := 487099/1000000) 286 262
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t318 : ((21093298587/1250000000000 : ℚ) : ℝ) ≤ stT286 318 := by
  have hc : ((150459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).1
  have hw2 : ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140193/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21093298587/1250000000000 : ℚ) : ℝ)
      = ((140193/2500000 : ℚ) : ℝ) * ((150459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c319 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-558207/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5407549/10000000) (δ := 14483/1000000000) (ψ := 487099/1000000) 286 262
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t319 : ((-312592181151/10000000000000 : ℚ) : ℝ) ≤ stT286 319 := by
  have hc : ((-558307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-312592181151/10000000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-558307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c320 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-24913/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1911339/2500000) (δ := 14483/1000000000) (ψ := 487099/1000000) 286 262
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t320 : ((-27856376127/500000000000 : ℚ) : ℝ) ≤ stT286 320 := by
  have hc : ((-49831/50000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27856376127/500000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-49831/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c321 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-27611/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1166333/2000000) (δ := 14413/1000000000) (ψ := 487099/1000000) 286 263
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t321 : ((-1541320179/40000000000 : ℚ) : ℝ) ≤ stT286 321 := by
  have hc : ((-5523/8000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1541320179/40000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-5523/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c322 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((63679/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3607729/10000000) (δ := 14413/1000000000) (ψ := 487099/1000000) 286 263
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t322 : ((17729520931/2500000000000 : ℚ) : ℝ) ≤ stT286 322 := by
  have hc : ((63629/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17729520931/2500000000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((63629/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c323 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((424617/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1390657/10000000) (δ := 14413/1000000000) (ψ := 487099/1000000) 286 263
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t323 : ((118117511369/2500000000000 : ℚ) : ℝ) ≤ stT286 323 := by
  have hc : ((424567/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).1
  have hw2 : ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278207/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118117511369/2500000000000 : ℚ) : ℝ)
      = ((278207/5000000 : ℚ) : ℝ) * ((424567/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c324 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((473373/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 819551/10000000) (δ := 14413/1000000000) (ψ := 487099/1000000) 286 263
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t324 : ((52591391853/1000000000000 : ℚ) : ℝ) ≤ stT286 324 := by
  have hc : ((473323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52591391853/1000000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((473323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c325 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((353807/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 604579/2000000) (δ := 14413/1000000000) (ψ := 487099/1000000) 286 263
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t325 : ((1962012729/100000000000 : ℚ) : ℝ) ≤ stT286 325 := by
  have hc : ((353707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1962012729/100000000000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((353707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c326 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-123571/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2609759/5000000) (δ := 14413/1000000000) (ψ := 487099/1000000) 286 263
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t326 : ((-17113380251/625000000000 : ℚ) : ℝ) ≤ stT286 326 := by
  have hc : ((-30899/62500 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).2
  have h0 : (0:ℝ) ≤ ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17113380251/625000000000 : ℚ) : ℝ)
      = ((553849/10000000 : ℚ) : ℝ) * ((-30899/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c327 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-984231/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 370471/500000) (δ := 14413/1000000000) (ψ := 487099/1000000) 286 263
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t327 : ((-272168505831/5000000000000 : ℚ) : ℝ) ≤ stT286 327 := by
  have hc : ((-984331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).2
  have h0 : (0:ℝ) ≤ ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-272168505831/5000000000000 : ℚ) : ℝ)
      = ((276501/5000000 : ℚ) : ℝ) * ((-984331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c328 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-191937/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -611529/1000000) (δ := 14497/1000000000) (ψ := 487099/1000000) 286 264
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t328 : ((-26498338499/625000000000 : ℚ) : ℝ) ≤ stT286 328 := by
  have hc : ((-95981/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26498338499/625000000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-95981/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c329 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-4707/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3938759/10000000) (δ := 7153/500000000) (ψ := 487099/1000000) 286 264
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t329 : ((-1325092813/5000000000000 : ℚ) : ℝ) ≤ stT286 329 := by
  have hc : ((-4807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).2
  have h0 : (0:ℝ) ≤ ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1325092813/5000000000000 : ℚ) : ℝ)
      = ((275659/5000000 : ℚ) : ℝ) * ((-4807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c330 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((30399/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -353761/2000000) (δ := 14497/1000000000) (ψ := 487099/1000000) 286 264
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t330 : ((3346373999/80000000000 : ℚ) : ℝ) ≤ stT286 330 := by
  have hc : ((6079/8000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).1
  have hw2 : ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((550481/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3346373999/80000000000 : ℚ) : ℝ)
      = ((550481/10000000 : ℚ) : ℝ) * ((6079/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c331 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((987571/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39457/1000000) (δ := 7153/500000000) (ψ := 487099/1000000) 286 264
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t331 : ((542762447679/10000000000000 : ℚ) : ℝ) ≤ stT286 331 := by
  have hc : ((987471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).1
  have hw2 : ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((549649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((542762447679/10000000000000 : ℚ) : ℝ)
      = ((549649/10000000 : ℚ) : ℝ) * ((987471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c332 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((4183/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2551439/10000000) (δ := 7153/500000000) (ψ := 487099/1000000) 286 264
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t332 : ((11476395931/400000000000 : ℚ) : ℝ) ≤ stT286 332 := by
  have hc : ((20911/40000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).1
  have hw2 : ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11476395931/400000000000 : ℚ) : ℝ)
      = ((548821/10000000 : ℚ) : ℝ) * ((20911/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c333 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-304987/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2350901/5000000) (δ := 14497/1000000000) (ψ := 487099/1000000) 286 264
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t333 : ((-167186760739/10000000000000 : ℚ) : ℝ) ≤ stT286 333 := by
  have hc : ((-305087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).2
  have h0 : (0:ℝ) ≤ ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167186760739/10000000000000 : ℚ) : ℝ)
      = ((547997/10000000 : ℚ) : ℝ) * ((-305087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c334 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-91977/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6845729/10000000) (δ := 7153/500000000) (ψ := 487099/1000000) 286 264
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t334 : ((-6291634839/125000000000 : ℚ) : ℝ) ≤ stT286 334 := by
  have hc : ((-91987/100000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).2
  have h0 : (0:ℝ) ≤ ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6291634839/125000000000 : ℚ) : ℝ)
      = ((68397/1250000 : ℚ) : ℝ) * ((-91987/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c335 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-56231/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -672467/1000000) (δ := 3601/250000000) (ψ := 487099/1000000) 286 265
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t335 : ((-122902910691/2500000000000 : ℚ) : ℝ) ≤ stT286 335 := by
  have hc : ((-224949/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).2
  have h0 : (0:ℝ) ≤ ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122902910691/2500000000000 : ℚ) : ℝ)
      = ((546359/10000000 : ℚ) : ℝ) * ((-224949/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c336 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-16467/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4593541/10000000) (δ := 3601/250000000) (ψ := 487099/1000000) 286 265
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t336 : ((-7189519337/500000000000 : ℚ) : ℝ) ≤ stT286 336 := by
  have hc : ((-65893/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).2
  have h0 : (0:ℝ) ≤ ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7189519337/500000000000 : ℚ) : ℝ)
      = ((109109/2000000 : ℚ) : ℝ) * ((-65893/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c337 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((275397/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -77147/312500) (δ := 3601/250000000) (ψ := 487099/1000000) 286 265
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t337 : ((74995436349/2500000000000 : ℚ) : ℝ) ≤ stT286 337 := by
  have hc : ((275347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).1
  have hw2 : ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((272367/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74995436349/2500000000000 : ℚ) : ℝ)
      = ((272367/5000000 : ℚ) : ℝ) * ((275347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c338 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((990203/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -350231/10000000) (δ := 14399/1000000000) (ψ := 487099/1000000) 286 265
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t338 : ((67318093073/1250000000000 : ℚ) : ℝ) ≤ stT286 338 := by
  have hc : ((990103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).1
  have hw2 : ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67991/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67318093073/1250000000000 : ℚ) : ℝ)
      = ((67991/1250000 : ℚ) : ℝ) * ((990103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c339 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((761717/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 881047/5000000) (δ := 3601/250000000) (ψ := 487099/1000000) 286 265
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t339 : ((661845173/16000000000 : ℚ) : ℝ) ≤ stT286 339 := by
  have hc : ((761617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).1
  have hw2 : ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((869/16000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((661845173/16000000000 : ℚ) : ℝ)
      = ((869/16000 : ℚ) : ℝ) * ((761617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c340 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((2943/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1934063/5000000) (δ := 14399/1000000000) (ψ := 487099/1000000) 286 265
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t340 : ((1589286343/1250000000000 : ℚ) : ℝ) ≤ stT286 340 := by
  have hc : ((5861/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).1
  have hw2 : ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1589286343/1250000000000 : ℚ) : ℝ)
      = ((271163/5000000 : ℚ) : ℝ) * ((5861/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c341 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-728671/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2983969/5000000) (δ := 14399/1000000000) (ψ := 487099/1000000) 286 265
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t341 : ((-394652088401/10000000000000 : ℚ) : ℝ) ≤ stT286 341 := by
  have hc : ((-728771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).2
  have h0 : (0:ℝ) ≤ ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-394652088401/10000000000000 : ℚ) : ℝ)
      = ((541531/10000000 : ℚ) : ℝ) * ((-728771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c342 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-996551/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7646291/10000000) (δ := 3623/250000000) (ψ := 487099/1000000) 286 266
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t342 : ((-538928065089/10000000000000 : ℚ) : ℝ) ≤ stT286 342 := by
  have hc : ((-996651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-538928065089/10000000000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-996651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c343 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-303661/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1111741/2000000) (δ := 14311/1000000000) (ψ := 487099/1000000) 286 266
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t343 : ((-3279775089/100000000000 : ℚ) : ℝ) ≤ stT286 343 := by
  have hc : ((-303711/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).2
  have h0 : (0:ℝ) ≤ ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3279775089/100000000000 : ℚ) : ℝ)
      = ((10799/200000 : ℚ) : ℝ) * ((-303711/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c344 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((44737/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3477197/10000000) (δ := 14311/1000000000) (ψ := 487099/1000000) 286 266
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t344 : ((3013382007/312500000000 : ℚ) : ℝ) ≤ stT286 344 := by
  have hc : ((5589/31250 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).1
  have hw2 : ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539163/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3013382007/312500000000 : ℚ) : ℝ)
      = ((539163/10000000 : ℚ) : ℝ) * ((5589/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c345 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((169379/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -280339/2000000) (δ := 14311/1000000000) (ψ := 487099/1000000) 286 266
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t345 : ((91179667779/2000000000000 : ℚ) : ℝ) ≤ stT286 345 := by
  have hc : ((169359/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91179667779/2000000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((169359/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c346 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((964543/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 667729/10000000) (δ := 3623/250000000) (ψ := 487099/1000000) 286 266
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t346 : ((518487450129/10000000000000 : ℚ) : ℝ) ≤ stT286 346 := by
  have hc : ((964443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((518487450129/10000000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((964443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c347 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((230139/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2731219/10000000) (δ := 3623/250000000) (ψ := 487099/1000000) 286 266
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t347 : ((30879554423/1250000000000 : ℚ) : ℝ) ≤ stT286 347 := by
  have hc : ((230089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30879554423/1250000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((230089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c348 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-337927/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 191551/400000) (δ := 14311/1000000000) (ψ := 487099/1000000) 286 266
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t348 : ((-181201739539/10000000000000 : ℚ) : ℝ) ≤ stT286 348 := by
  have hc : ((-338027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).2
  have h0 : (0:ℝ) ≤ ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181201739539/10000000000000 : ℚ) : ℝ)
      = ((536057/10000000 : ℚ) : ℝ) * ((-338027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c349 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-459471/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6840467/10000000) (δ := 3623/250000000) (ψ := 487099/1000000) 286 266
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t349 : ((-30747009631/625000000000 : ℚ) : ℝ) ≤ stT286 349 := by
  have hc : ((-459521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).2
  have h0 : (0:ℝ) ≤ ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30747009631/625000000000 : ℚ) : ℝ)
      = ((66911/1250000 : ℚ) : ℝ) * ((-459521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c350 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-457981/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3410869/5000000) (δ := 2877/200000000) (ψ := 487099/1000000) 286 267
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t350 : ((-244828104213/5000000000000 : ℚ) : ℝ) ≤ stT286 350 := by
  have hc : ((-458031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244828104213/5000000000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-458031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c351 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-335289/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4781771/10000000) (δ := 7209/500000000) (ψ := 487099/1000000) 286 267
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t351 : ((-179017568029/10000000000000 : ℚ) : ℝ) ≤ stT286 351 := by
  have hc : ((-335389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179017568029/10000000000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-335389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c352 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((454427/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -686917/2500000) (δ := 2877/200000000) (ψ := 487099/1000000) 286 267
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t352 : ((242156745327/10000000000000 : ℚ) : ℝ) ≤ stT286 352 := by
  have hc : ((454327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).1
  have hw2 : ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((533001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242156745327/10000000000000 : ℚ) : ℝ)
      = ((533001/10000000 : ℚ) : ℝ) * ((454327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c353 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((191779/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -179821/2500000) (δ := 7209/500000000) (ψ := 487099/1000000) 286 267
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t353 : ((51031480357/1000000000000 : ℚ) : ℝ) ≤ stT286 353 := by
  have hc : ((191759/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).1
  have hw2 : ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((266123/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51031480357/1000000000000 : ℚ) : ℝ)
      = ((266123/5000000 : ℚ) : ℝ) * ((191759/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c354 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((867147/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1303379/10000000) (δ := 2877/200000000) (ψ := 487099/1000000) 286 267
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t354 : ((230415139109/5000000000000 : ℚ) : ℝ) ≤ stT286 354 := by
  have hc : ((867047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).1
  have hw2 : ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((265747/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230415139109/5000000000000 : ℚ) : ℝ)
      = ((265747/5000000 : ℚ) : ℝ) * ((867047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c355 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((751/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3320251/10000000) (δ := 2877/200000000) (ψ := 487099/1000000) 286 267
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t355 : ((796845773/62500000000 : ℚ) : ℝ) ≤ stT286 355 := by
  have hc : ((12011/50000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).1
  have hw2 : ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66343/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((796845773/62500000000 : ℚ) : ℝ)
      = ((66343/1250000 : ℚ) : ℝ) * ((12011/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c356 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-532729/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2665773/5000000) (δ := 2877/200000000) (ψ := 487099/1000000) 286 267
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t356 : ((-282398837171/10000000000000 : ℚ) : ℝ) ≤ stT286 356 := by
  have hc : ((-532829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).2
  have h0 : (0:ℝ) ≤ ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-282398837171/10000000000000 : ℚ) : ℝ)
      = ((529999/10000000 : ℚ) : ℝ) * ((-532829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c357 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-61169/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7337121/10000000) (δ := 2877/200000000) (ψ := 487099/1000000) 286 267
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t357 : ((-129509717157/2500000000000 : ℚ) : ℝ) ≤ stT286 357 := by
  have hc : ((-244701/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).2
  have h0 : (0:ℝ) ≤ ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129509717157/2500000000000 : ℚ) : ℝ)
      = ((529257/10000000 : ℚ) : ℝ) * ((-244701/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c358 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-6633/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1592711/2500000) (δ := 7163/500000000) (ψ := 487099/1000000) 286 268
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t358 : ((-17530380373/400000000000 : ℚ) : ℝ) ≤ stT286 358 := by
  have hc : ((-33169/40000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).2
  have h0 : (0:ℝ) ≤ ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17530380373/400000000000 : ℚ) : ℝ)
      = ((528517/10000000 : ℚ) : ℝ) * ((-33169/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c359 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-89403/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4376423/10000000) (δ := 7163/500000000) (ψ := 487099/1000000) 286 268
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t359 : ((-2360575217/250000000000 : ℚ) : ℝ) ≤ stT286 359 := by
  have hc : ((-89453/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).2
  have h0 : (0:ℝ) ≤ ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2360575217/250000000000 : ℚ) : ℝ)
      = ((26389/500000 : ℚ) : ℝ) * ((-89453/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c360 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((288803/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -596877/2500000) (δ := 14477/1000000000) (ψ := 487099/1000000) 286 268
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t360 : ((76093056819/2500000000000 : ℚ) : ℝ) ≤ stT286 360 := by
  have hc : ((288753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).1
  have hw2 : ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76093056819/2500000000000 : ℚ) : ℝ)
      = ((263523/5000000 : ℚ) : ℝ) * ((288753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c361 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((12337/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -404169/10000000) (δ := 7163/500000000) (ψ := 487099/1000000) 286 268
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t361 : ((5193992209/100000000000 : ℚ) : ℝ) ≤ stT286 361 := by
  have hc : ((49343/50000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5193992209/100000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((49343/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c362 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((404163/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 314747/2000000) (δ := 14477/1000000000) (ψ := 487099/1000000) 286 268
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t362 : ((53099235861/1250000000000 : ℚ) : ℝ) ≤ stT286 362 := by
  have hc : ((404113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53099235861/1250000000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((404113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c363 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((75877/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1773067/5000000) (δ := 14477/1000000000) (ψ := 487099/1000000) 286 268
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t363 : ((39798786701/5000000000000 : ℚ) : ℝ) ≤ stT286 363 := by
  have hc : ((75827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).1
  have hw2 : ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((524863/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39798786701/5000000000000 : ℚ) : ℝ)
      = ((524863/10000000 : ℚ) : ℝ) * ((75827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c364 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-592729/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5513099/10000000) (δ := 14477/1000000000) (ψ := 487099/1000000) 286 268
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t364 : ((-310727170547/10000000000000 : ℚ) : ℝ) ≤ stT286 364 := by
  have hc : ((-592829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-310727170547/10000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-592829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c365 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-494257/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3737351/5000000) (δ := 7163/500000000) (ψ := 487099/1000000) 286 268
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t365 : ((-8085379599/156250000000 : ℚ) : ℝ) ≤ stT286 365 := by
  have hc : ((-494307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8085379599/156250000000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-494307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c366 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-161513/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6277021/10000000) (δ := 14433/1000000000) (ψ := 487099/1000000) 286 269
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t366 : ((-84434752897/2000000000000 : ℚ) : ℝ) ≤ stT286 366 := by
  have hc : ((-161533/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84434752897/2000000000000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-161533/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c367 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-19873/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33798/78125) (δ := 1437/100000000) (ψ := 487099/1000000) 286 269
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t367 : ((-5190075729/625000000000 : ℚ) : ℝ) ≤ stT286 367 := by
  have hc : ((-39771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5190075729/625000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-39771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c368 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((289937/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2380557/10000000) (δ := 14433/1000000000) (ψ := 487099/1000000) 286 269
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t368 : ((75557017341/2500000000000 : ℚ) : ℝ) ≤ stT286 368 := by
  have hc : ((289887/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75557017341/2500000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((289887/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c369 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((492267/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -220131/5000000) (δ := 1437/100000000) (ψ := 487099/1000000) 286 269
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t369 : ((256237833643/5000000000000 : ℚ) : ℝ) ≤ stT286 369 := by
  have hc : ((492217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((256237833643/5000000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((492217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c370 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((165301/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 747407/5000000) (δ := 1437/100000000) (ψ := 487099/1000000) 286 269
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t370 : ((687403679/16000000000 : ℚ) : ℝ) ≤ stT286 370 := by
  have hc : ((165281/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).1
  have hw2 : ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((4159/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((687403679/16000000000 : ℚ) : ℝ)
      = ((4159/80000 : ℚ) : ℝ) * ((165281/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c371 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((199607/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3424599/10000000) (δ := 1437/100000000) (ψ := 487099/1000000) 286 269
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t371 : ((51789423609/5000000000000 : ℚ) : ℝ) ≤ stT286 371 := by
  have hc : ((199507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).1
  have hw2 : ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((259587/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51789423609/5000000000000 : ℚ) : ℝ)
      = ((259587/5000000 : ℚ) : ℝ) * ((199507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c372 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-33669/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1337309/2500000) (δ := 1437/100000000) (ψ := 487099/1000000) 286 269
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t372 : ((-17459808919/625000000000 : ℚ) : ℝ) ≤ stT286 372 := by
  have hc : ((-134701/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17459808919/625000000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-134701/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c373 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-972723/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 290749/400000) (δ := 1437/100000000) (ψ := 487099/1000000) 286 269
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t373 : ((-503709265763/10000000000000 : ℚ) : ℝ) ≤ stT286 373 := by
  have hc : ((-972823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).2
  have h0 : (0:ℝ) ≤ ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-503709265763/10000000000000 : ℚ) : ℝ)
      = ((517781/10000000 : ℚ) : ℝ) * ((-972823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c374 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-172399/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6524969/10000000) (δ := 14463/1000000000) (ψ := 487099/1000000) 286 270
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t374 : ((-2786118621/62500000000 : ℚ) : ℝ) ≤ stT286 374 := by
  have hc : ((-172419/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2786118621/62500000000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-172419/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c375 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-136007/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -576963/1250000) (δ := 717/50000000) (ψ := 487099/1000000) 286 270
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t375 : ((-35129781343/2500000000000 : ℚ) : ℝ) ≤ stT286 375 := by
  have hc : ((-136057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).2
  have h0 : (0:ℝ) ≤ ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35129781343/2500000000000 : ℚ) : ℝ)
      = ((258199/5000000 : ℚ) : ℝ) * ((-136057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c376 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((93447/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -677897/2500000) (δ := 14463/1000000000) (ψ := 487099/1000000) 286 270
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t376 : ((4818123817/200000000000 : ℚ) : ℝ) ≤ stT286 376 := by
  have hc : ((93427/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4818123817/200000000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((93427/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c377 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((189529/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -203137/2500000) (δ := 14463/1000000000) (ψ := 487099/1000000) 286 270
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t377 : ((48801031117/1000000000000 : ℚ) : ℝ) ≤ stT286 377 := by
  have hc : ((189509/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48801031117/1000000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((189509/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c378 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((907881/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1081487/10000000) (δ := 14463/1000000000) (ψ := 487099/1000000) 286 270
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t378 : ((58363963833/1250000000000 : ℚ) : ℝ) ≤ stT286 378 := by
  have hc : ((907781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58363963833/1250000000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((907781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c379 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((373297/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2970589/10000000) (δ := 717/50000000) (ψ := 487099/1000000) 286 270
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t379 : ((38339647401/2000000000000 : ℚ) : ℝ) ≤ stT286 379 := by
  have hc : ((373197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).1
  have hw2 : ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102733/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38339647401/2000000000000 : ℚ) : ℝ)
      = ((102733/2000000 : ℚ) : ℝ) * ((373197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c380 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-362593/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2427307/5000000) (δ := 717/50000000) (ψ := 487099/1000000) 286 270
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t380 : ((-18605788207/1000000000000 : ℚ) : ℝ) ≤ stT286 380 := by
  have hc : ((-362693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18605788207/1000000000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-362693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c381 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-901267/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1346741/2000000) (δ := 14463/1000000000) (ψ := 487099/1000000) 286 270
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t381 : ((-115446183993/2500000000000 : ℚ) : ℝ) ≤ stT286 381 := by
  have hc : ((-901367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115446183993/2500000000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-901367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c382 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-238717/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1775007/2500000) (δ := 14447/1000000000) (ψ := 487099/1000000) 286 271
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t382 : ((-12215115059/250000000000 : ℚ) : ℝ) ≤ stT286 382 := by
  have hc : ((-119371/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).2
  have h0 : (0:ℝ) ≤ ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12215115059/250000000000 : ℚ) : ℝ)
      = ((102329/2000000 : ℚ) : ℝ) * ((-119371/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c383 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-498203/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1307701/2500000) (δ := 3589/250000000) (ψ := 487099/1000000) 286 271
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t383 : ((-254621372031/10000000000000 : ℚ) : ℝ) ≤ stT286 383 := by
  have hc : ((-498303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).2
  have h0 : (0:ℝ) ≤ ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-254621372031/10000000000000 : ℚ) : ℝ)
      = ((510977/10000000 : ℚ) : ℝ) * ((-498303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c384 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((111187/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -336637/1000000) (δ := 3589/250000000) (ψ := 487099/1000000) 286 271
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t384 : ((5671432247/500000000000 : ℚ) : ℝ) ≤ stT286 384 := by
  have hc : ((111137/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).1
  have hw2 : ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5671432247/500000000000 : ℚ) : ℝ)
      = ((51031/1000000 : ℚ) : ℝ) * ((111137/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c385 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((823797/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -753399/5000000) (δ := 3589/250000000) (ψ := 487099/1000000) 286 271
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t385 : ((419794704959/10000000000000 : ℚ) : ℝ) ≤ stT286 385 := by
  have hc : ((823697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((419794704959/10000000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((823697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c386 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((247583/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 43489/1250000) (δ := 3589/250000000) (ψ := 487099/1000000) 286 271
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t386 : ((31500889047/625000000000 : ℚ) : ℝ) ≤ stT286 386 := by
  have hc : ((123779/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).1
  have hw2 : ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((254493/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31500889047/625000000000 : ℚ) : ℝ)
      = ((254493/5000000 : ℚ) : ℝ) * ((123779/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c387 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((637819/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 274729/1250000) (δ := 14447/1000000000) (ψ := 487099/1000000) 286 271
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t387 : ((40521302979/1250000000000 : ℚ) : ℝ) ≤ stT286 387 := by
  have hc : ((637719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).1
  have hw2 : ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((63541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40521302979/1250000000000 : ℚ) : ℝ)
      = ((63541/1250000 : ℚ) : ℝ) * ((637719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c388 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-29/625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 505379/1250000) (δ := 3589/250000000) (ψ := 487099/1000000) 286 271
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t388 : ((-23606841/10000000000 : ℚ) : ℝ) ≤ stT286 388 := by
  have hc : ((-93/2000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).2
  have h0 : (0:ℝ) ≤ ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23606841/10000000000 : ℚ) : ℝ)
      = ((253837/5000000 : ℚ) : ℝ) * ((-93/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c389 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-88139/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2941721/5000000) (δ := 3589/250000000) (ψ := 487099/1000000) 286 271
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t389 : ((-89389323363/2500000000000 : ℚ) : ℝ) ≤ stT286 389 := by
  have hc : ((-176303/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89389323363/2500000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-176303/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c390 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-499273/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7719133/10000000) (δ := 3589/250000000) (ψ := 487099/1000000) 286 271
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t390 : ((-25284218751/500000000000 : ℚ) : ℝ) ≤ stT286 390 := by
  have hc : ((-499323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).2
  have h0 : (0:ℝ) ≤ ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25284218751/500000000000 : ℚ) : ℝ)
      = ((50637/1000000 : ℚ) : ℝ) * ((-499323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c391 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-778547/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3078929/5000000) (δ := 7177/500000000) (ψ := 487099/1000000) 286 272
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t391 : ((-196889459067/5000000000000 : ℚ) : ℝ) ≤ stT286 391 := by
  have hc : ((-778647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).2
  have h0 : (0:ℝ) ≤ ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-196889459067/5000000000000 : ℚ) : ℝ)
      = ((252861/5000000 : ℚ) : ℝ) * ((-778647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c392 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-20139/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2165767/5000000) (δ := 14449/1000000000) (ψ := 487099/1000000) 286 272
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t392 : ((-20356118331/2500000000000 : ℚ) : ℝ) ≤ stT286 392 := by
  have hc : ((-40303/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).2
  have h0 : (0:ℝ) ≤ ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20356118331/2500000000000 : ℚ) : ℝ)
      = ((505077/10000000 : ℚ) : ℝ) * ((-40303/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c393 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((26849/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2509857/10000000) (δ := 14449/1000000000) (ψ := 487099/1000000) 286 272
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t393 : ((3385249863/125000000000 : ℚ) : ℝ) ≤ stT286 393 := by
  have hc : ((6711/12500 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3385249863/125000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((6711/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c394 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((240461/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -692827/10000000) (δ := 7177/500000000) (ψ := 487099/1000000) 286 272
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t394 : ((1892652083/39062500000 : ℚ) : ℝ) ≤ stT286 394 := by
  have hc : ((60109/62500 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).1
  have hw2 : ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31487/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1892652083/39062500000 : ℚ) : ℝ)
      = ((31487/625000 : ℚ) : ℝ) * ((60109/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c395 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((56337/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 223911/2000000) (δ := 7177/500000000) (ψ := 487099/1000000) 286 272
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t395 : ((56686084371/1250000000000 : ℚ) : ℝ) ≤ stT286 395 := by
  have hc : ((225323/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).1
  have hw2 : ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56686084371/1250000000000 : ℚ) : ℝ)
      = ((251577/5000000 : ℚ) : ℝ) * ((225323/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c396 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((48657/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 365929/1250000) (δ := 14449/1000000000) (ψ := 487099/1000000) 286 272
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t396 : ((24444736851/1250000000000 : ℚ) : ℝ) ≤ stT286 396 := by
  have hc : ((97289/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).1
  have hw2 : ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251259/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24444736851/1250000000000 : ℚ) : ℝ)
      = ((251259/5000000 : ℚ) : ℝ) * ((97289/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c397 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-7899/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2365331/5000000) (δ := 14449/1000000000) (ψ := 487099/1000000) 286 272
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t397 : ((-3965652229/250000000000 : ℚ) : ℝ) ≤ stT286 397 := by
  have hc : ((-15803/50000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3965652229/250000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-15803/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c398 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-107863/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6529459/10000000) (δ := 14449/1000000000) (ψ := 487099/1000000) 286 272
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t398 : ((-21629253501/500000000000 : ℚ) : ℝ) ≤ stT286 398 := by
  have hc : ((-215751/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).2
  have h0 : (0:ℝ) ≤ ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21629253501/500000000000 : ℚ) : ℝ)
      = ((100251/2000000 : ℚ) : ℝ) * ((-215751/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c399 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-982403/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7384283/10000000) (δ := 14341/1000000000) (ψ := 487099/1000000) 286 273
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t399 : ((-491867529381/10000000000000 : ℚ) : ℝ) ≤ stT286 399 := by
  have hc : ((-982503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).2
  have h0 : (0:ℝ) ≤ ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-491867529381/10000000000000 : ℚ) : ℝ)
      = ((500627/10000000 : ℚ) : ℝ) * ((-982503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c400 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-123731/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2797283/5000000) (δ := 7231/500000000) (ψ := 487099/1000000) 286 273
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t400 : ((-61875623751/2000000000000 : ℚ) : ℝ) ≤ stT286 400 := by
  have hc : ((-123751/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61875623751/2000000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-123751/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c401 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((23533/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3809283/10000000) (δ := 14341/1000000000) (ψ := 487099/1000000) 286 273
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t401 : ((732927913/312500000000 : ℚ) : ℝ) ≤ stT286 401 := by
  have hc : ((23483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).1
  have hw2 : ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31211/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((732927913/312500000000 : ℚ) : ℝ)
      = ((31211/625000 : ℚ) : ℝ) * ((23483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c402 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((688483/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -253563/1250000) (δ := 14341/1000000000) (ψ := 487099/1000000) 286 273
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t402 : ((171666887391/5000000000000 : ℚ) : ℝ) ≤ stT286 402 := by
  have hc : ((688383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).1
  have hw2 : ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((249377/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171666887391/5000000000000 : ℚ) : ℝ)
      = ((249377/5000000 : ℚ) : ℝ) * ((688383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c403 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((994921/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -126043/5000000) (δ := 7231/500000000) (ψ := 487099/1000000) 286 273
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t403 : ((99111031767/2000000000000 : ℚ) : ℝ) ≤ stT286 403 := by
  have hc : ((994821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).1
  have hw2 : ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((99627/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99111031767/2000000000000 : ℚ) : ℝ)
      = ((99627/2000000 : ℚ) : ℝ) * ((994821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c404 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((164163/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 759949/5000000) (δ := 14341/1000000000) (ψ := 487099/1000000) 286 273
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t404 : ((40832048537/1000000000000 : ℚ) : ℝ) ≤ stT286 404 := by
  have hc : ((164143/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).1
  have hw2 : ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((248759/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40832048537/1000000000000 : ℚ) : ℝ)
      = ((248759/5000000 : ℚ) : ℝ) * ((164143/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c405 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((15813/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3287521/10000000) (δ := 14341/1000000000) (ψ := 487099/1000000) 286 273
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t405 : ((31417685981/2500000000000 : ℚ) : ℝ) ≤ stT286 405 := by
  have hc : ((63227/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31417685981/2500000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((63227/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c406 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-43453/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5050783/10000000) (δ := 7231/500000000) (ψ := 487099/1000000) 286 273
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t406 : ((-5392584799/250000000000 : ℚ) : ℝ) ≤ stT286 406 := by
  have hc : ((-43463/100000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).2
  have h0 : (0:ℝ) ≤ ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5392584799/250000000000 : ℚ) : ℝ)
      = ((124073/2500000 : ℚ) : ℝ) * ((-43463/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c407 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-28563/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6809683/10000000) (δ := 7231/500000000) (ψ := 487099/1000000) 286 273
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t407 : ((-56638855889/1250000000000 : ℚ) : ℝ) ≤ stT286 407 := by
  have hc : ((-228529/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).2
  have h0 : (0:ℝ) ≤ ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56638855889/1250000000000 : ℚ) : ℝ)
      = ((247841/5000000 : ℚ) : ℝ) * ((-228529/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c408 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-239977/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7143671/10000000) (δ := 7217/500000000) (ψ := 487099/1000000) 286 274
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t408 : ((-29704687537/625000000000 : ℚ) : ℝ) ≤ stT286 408 := by
  have hc : ((-120001/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).2
  have h0 : (0:ℝ) ≤ ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29704687537/625000000000 : ℚ) : ℝ)
      = ((247537/5000000 : ℚ) : ℝ) * ((-120001/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c409 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-276743/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5393351/10000000) (δ := 7217/500000000) (ψ := 487099/1000000) 286 274
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t409 : ((-136865557917/5000000000000 : ℚ) : ℝ) ≤ stT286 409 := by
  have hc : ((-276793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).2
  have h0 : (0:ℝ) ≤ ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136865557917/5000000000000 : ℚ) : ℝ)
      = ((494469/10000000 : ℚ) : ℝ) * ((-276793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c410 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((22327/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3647321/10000000) (δ := 7217/500000000) (ψ := 487099/1000000) 286 274
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t410 : ((1377078031/250000000000 : ℚ) : ℝ) ≤ stT286 410 := by
  have hc : ((22307/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).1
  have hw2 : ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61733/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1377078031/250000000000 : ℚ) : ℝ)
      = ((61733/1250000 : ℚ) : ℝ) * ((22307/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c411 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((180829/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1905509/10000000) (δ := 14369/1000000000) (ψ := 487099/1000000) 286 274
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t411 : ((22295980863/625000000000 : ℚ) : ℝ) ≤ stT286 411 := by
  have hc : ((45201/62500 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).1
  have hw2 : ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((493263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22295980863/625000000000 : ℚ) : ℝ)
      = ((493263/10000000 : ℚ) : ℝ) * ((45201/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c412 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((997743/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41997/2500000) (δ := 7217/500000000) (ψ := 487099/1000000) 286 274
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t412 : ((61437848869/1250000000000 : ℚ) : ℝ) ≤ stT286 412 := by
  have hc : ((997643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).1
  have hw2 : ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61583/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61437848869/1250000000000 : ℚ) : ℝ)
      = ((61583/1250000 : ℚ) : ℝ) * ((997643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c413 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((12661/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 313063/2000000) (δ := 7217/500000000) (ψ := 487099/1000000) 286 274
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t413 : ((99668662917/2500000000000 : ℚ) : ℝ) ≤ stT286 413 := by
  have hc : ((202551/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).1
  have hw2 : ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((492067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99668662917/2500000000000 : ℚ) : ℝ)
      = ((492067/10000000 : ℚ) : ℝ) * ((202551/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c414 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((250317/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3294471/10000000) (δ := 7217/500000000) (ψ := 487099/1000000) 286 274
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t414 : ((122974899641/10000000000000 : ℚ) : ℝ) ≤ stT286 414 := by
  have hc : ((250217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).1
  have hw2 : ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((491473/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122974899641/10000000000000 : ℚ) : ℝ)
      = ((491473/10000000 : ℚ) : ℝ) * ((250217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c415 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-423219/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 125487/250000) (δ := 7217/500000000) (ψ := 487099/1000000) 286 274
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t415 : ((-207799254039/10000000000000 : ℚ) : ℝ) ≤ stT286 415 := by
  have hc : ((-423319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207799254039/10000000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-423319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c416 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-451201/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6740271/10000000) (δ := 14369/1000000000) (ψ := 487099/1000000) 286 274
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t416 : ((-221244304041/5000000000000 : ℚ) : ℝ) ≤ stT286 416 := by
  have hc : ((-451251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221244304041/5000000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-451251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c417 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-242763/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7250977/10000000) (δ := 3619/250000000) (ψ := 487099/1000000) 286 275
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t417 : ((-29723502991/625000000000 : ℚ) : ℝ) ≤ stT286 417 := by
  have hc : ((-60697/62500 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29723502991/625000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-60697/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c418 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-600853/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5538409/10000000) (δ := 3619/250000000) (ψ := 487099/1000000) 286 275
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t418 : ((-73483931887/2500000000000 : ℚ) : ℝ) ≤ stT286 418 := by
  have hc : ((-600953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).2
  have h0 : (0:ℝ) ≤ ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73483931887/2500000000000 : ℚ) : ℝ)
      = ((122279/2500000 : ℚ) : ℝ) * ((-600953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c419 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((1941/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3829917/10000000) (δ := 14327/1000000000) (ψ := 487099/1000000) 286 275
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t419 : ((59112251/31250000000 : ℚ) : ℝ) ≤ stT286 419 := by
  have hc : ((121/3125 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59112251/31250000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((121/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c420 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((659833/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4251/20000) (δ := 14327/1000000000) (ψ := 487099/1000000) 286 275
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t420 : ((6438334347/200000000000 : ℚ) : ℝ) ≤ stT286 420 := by
  have hc : ((659733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6438334347/200000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((659733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c421 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((492787/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -212579/5000000) (δ := 3619/250000000) (ψ := 487099/1000000) 286 275
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t421 : ((24014523169/500000000000 : ℚ) : ℝ) ≤ stT286 421 := by
  have hc : ((492737/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24014523169/500000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((492737/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c422 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((87349/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1271179/10000000) (δ := 14327/1000000000) (ψ := 487099/1000000) 286 275
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t422 : ((5314490811/125000000000 : ℚ) : ℝ) ≤ stT286 422 := by
  have hc : ((87339/100000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5314490811/125000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((87339/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c423 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((93987/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2963441/10000000) (δ := 14327/1000000000) (ψ := 487099/1000000) 286 275
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t423 : ((2855364237/156250000000 : ℚ) : ℝ) ≤ stT286 423 := by
  have hc : ((46981/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2855364237/156250000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((46981/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c424 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-71467/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4651771/10000000) (δ := 3619/250000000) (ψ := 487099/1000000) 286 275
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t424 : ((-8679897339/625000000000 : ℚ) : ℝ) ≤ stT286 424 := by
  have hc : ((-17873/62500 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).2
  have h0 : (0:ℝ) ≤ ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8679897339/625000000000 : ℚ) : ℝ)
      = ((485643/10000000 : ℚ) : ℝ) * ((-17873/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c425 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-32851/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 198003/312500) (δ := 14327/1000000000) (ψ := 487099/1000000) 286 275
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t425 : ((-199213007/5000000000 : ℚ) : ℝ) ≤ stT286 425 := by
  have hc : ((-6571/8000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199213007/5000000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-6571/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c426 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-15592/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3845737/5000000) (δ := 14383/1000000000) (ψ := 487099/1000000) 286 276
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t426 : ((-60440897747/1250000000000 : ℚ) : ℝ) ≤ stT286 426 := by
  have hc : ((-249497/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60440897747/1250000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-249497/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c427 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-741437/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3007507/5000000) (δ := 721/50000000) (ψ := 487099/1000000) 286 276
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t427 : ((-179427483279/5000000000000 : ℚ) : ℝ) ≤ stT286 427 := by
  have hc : ((-741537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179427483279/5000000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-741537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c428 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-82731/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4342557/10000000) (δ := 14383/1000000000) (ψ := 487099/1000000) 286 276
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t428 : ((-40013769189/5000000000000 : ℚ) : ℝ) ≤ stT286 428 := by
  have hc : ((-82781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40013769189/5000000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-82781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c429 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((240257/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -267389/1000000) (δ := 14383/1000000000) (ψ := 487099/1000000) 286 276
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t429 : ((28993225107/1250000000000 : ℚ) : ℝ) ≤ stT286 429 := by
  have hc : ((240207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).1
  have hw2 : ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((120701/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28993225107/1250000000000 : ℚ) : ℝ)
      = ((120701/2500000 : ℚ) : ℝ) * ((240207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c430 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((919629/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -252289/2500000) (δ := 721/50000000) (ψ := 487099/1000000) 286 276
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t430 : ((221717752009/5000000000000 : ℚ) : ℝ) ≤ stT286 430 := by
  have hc : ((919529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).1
  have hw2 : ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((241121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((221717752009/5000000000000 : ℚ) : ℝ)
      = ((241121/5000000 : ℚ) : ℝ) * ((919529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c431 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((966221/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 325823/5000000) (δ := 721/50000000) (ψ := 487099/1000000) 286 276
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t431 : ((465364061643/10000000000000 : ℚ) : ℝ) ≤ stT286 431 := by
  have hc : ((966121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((465364061643/10000000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((966121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c432 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((603061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2308659/10000000) (δ := 14383/1000000000) (ψ := 487099/1000000) 286 276
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t432 : ((2320796889/80000000000 : ℚ) : ℝ) ≤ stT286 432 := by
  have hc : ((602961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2320796889/80000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((602961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c433 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-3489/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1980941/5000000) (δ := 14383/1000000000) (ψ := 487099/1000000) 286 276
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t433 : ((-84436149/125000000000 : ℚ) : ℝ) ≤ stT286 433 := by
  have hc : ((-1757/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).2
  have h0 : (0:ℝ) ≤ ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84436149/125000000000 : ℚ) : ℝ)
      = ((48057/1000000 : ℚ) : ℝ) * ((-1757/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c434 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-623883/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1402811/2500000) (δ := 14383/1000000000) (ψ := 487099/1000000) 286 276
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t434 : ((-18720113983/625000000000 : ℚ) : ℝ) ≤ stT286 434 := by
  have hc : ((-623983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).2
  have h0 : (0:ℝ) ≤ ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18720113983/625000000000 : ℚ) : ℝ)
      = ((30001/625000 : ℚ) : ℝ) * ((-623983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c435 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-971607/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 453551/625000) (δ := 721/50000000) (ψ := 487099/1000000) 286 276
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t435 : ((-58237315631/1250000000000 : ℚ) : ℝ) ≤ stT286 435 := by
  have hc : ((-971707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).2
  have h0 : (0:ℝ) ≤ ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58237315631/1250000000000 : ℚ) : ℝ)
      = ((59933/1250000 : ℚ) : ℝ) * ((-971707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c436 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-182793/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1702341/2500000) (δ := 14313/1000000000) (ψ := 487099/1000000) 286 277
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t436 : ((-43775852541/1000000000000 : ℚ) : ℝ) ≤ stT286 436 := by
  have hc : ((-182813/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).2
  have h0 : (0:ℝ) ≤ ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43775852541/1000000000000 : ℚ) : ℝ)
      = ((239457/5000000 : ℚ) : ℝ) * ((-182813/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c437 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-477451/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -517137/1000000) (δ := 1449/100000000) (ψ := 487099/1000000) 286 277
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t437 : ((-45688736823/2000000000000 : ℚ) : ℝ) ≤ stT286 437 := by
  have hc : ((-477551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).2
  have h0 : (0:ℝ) ≤ ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45688736823/2000000000000 : ℚ) : ℝ)
      = ((95673/2000000 : ℚ) : ℝ) * ((-477551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c438 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((31071/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3537023/10000000) (δ := 1449/100000000) (ψ := 487099/1000000) 286 277
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t438 : ((7418363359/1000000000000 : ℚ) : ℝ) ≤ stT286 438 := by
  have hc : ((31051/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).1
  have hw2 : ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((238909/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7418363359/1000000000000 : ℚ) : ℝ)
      = ((238909/5000000 : ℚ) : ℝ) * ((31051/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c439 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((180763/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -953233/5000000) (δ := 14313/1000000000) (ψ := 487099/1000000) 286 277
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t439 : ((43130683737/1250000000000 : ℚ) : ℝ) ≤ stT286 439 := by
  have hc : ((90369/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).1
  have hw2 : ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((477273/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43130683737/1250000000000 : ℚ) : ℝ)
      = ((477273/10000000 : ℚ) : ℝ) * ((90369/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c440 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((993751/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -139813/5000000) (δ := 1449/100000000) (ψ := 487099/1000000) 286 277
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t440 : ((473704234881/10000000000000 : ℚ) : ℝ) ≤ stT286 440 := by
  have hc : ((993651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).1
  have hw2 : ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((473704234881/10000000000000 : ℚ) : ℝ)
      = ((476731/10000000 : ℚ) : ℝ) * ((993651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c441 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((214761/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 268699/2000000) (δ := 14313/1000000000) (ψ := 487099/1000000) 286 277
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t441 : ((639094599/15625000000 : ℚ) : ℝ) ≤ stT286 441 := by
  have hc : ((13421/15625 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).1
  have hw2 : ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((47619/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((639094599/15625000000 : ℚ) : ℝ)
      = ((47619/1000000 : ℚ) : ℝ) * ((13421/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c442 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((376123/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 296297/1000000) (δ := 14313/1000000000) (ψ := 487099/1000000) 286 277
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t442 : ((178855715973/10000000000000 : ℚ) : ℝ) ≤ stT286 442 := by
  have hc : ((376023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).1
  have hw2 : ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((475651/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178855715973/10000000000000 : ℚ) : ℝ)
      = ((475651/10000000 : ℚ) : ℝ) * ((376023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c443 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-257779/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4578799/10000000) (δ := 1449/100000000) (ψ := 487099/1000000) 286 277
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t443 : ((-24504436217/2000000000000 : ℚ) : ℝ) ≤ stT286 443 := by
  have hc : ((-257879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).2
  have h0 : (0:ℝ) ≤ ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24504436217/2000000000000 : ℚ) : ℝ)
      = ((95023/2000000 : ℚ) : ℝ) * ((-257879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c444 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-786793/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6190981/10000000) (δ := 1449/100000000) (ψ := 487099/1000000) 286 277
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t444 : ((-373442893047/10000000000000 : ℚ) : ℝ) ≤ stT286 444 := by
  have hc : ((-786893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-373442893047/10000000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-786893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c445 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-999763/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1949879/2500000) (δ := 14313/1000000000) (ψ := 487099/1000000) 286 277
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t445 : ((-236990527849/5000000000000 : ℚ) : ℝ) ≤ stT286 445 := by
  have hc : ((-999863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).2
  have h0 : (0:ℝ) ≤ ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236990527849/5000000000000 : ℚ) : ℝ)
      = ((237023/5000000 : ℚ) : ℝ) * ((-999863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c446 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-813763/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6303487/10000000) (δ := 7203/500000000) (ψ := 487099/1000000) 286 278
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t446 : ((-192687762291/5000000000000 : ℚ) : ℝ) ≤ stT286 446 := by
  have hc : ((-813863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).2
  have h0 : (0:ℝ) ≤ ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192687762291/5000000000000 : ℚ) : ℝ)
      = ((236757/5000000 : ℚ) : ℝ) * ((-813863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c447 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-38141/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4702173/10000000) (δ := 7203/500000000) (ψ := 487099/1000000) 286 278
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t447 : ((-4511498761/312500000000 : ℚ) : ℝ) ≤ stT286 447 := by
  have hc : ((-76307/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).2
  have h0 : (0:ℝ) ≤ ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4511498761/312500000000 : ℚ) : ℝ)
      = ((59123/1250000 : ℚ) : ℝ) * ((-76307/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c448 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((161573/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1552181/5000000) (δ := 14397/1000000000) (ψ := 487099/1000000) 286 278
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t448 : ((15262469793/1000000000000 : ℚ) : ℝ) ≤ stT286 448 := by
  have hc : ((161523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15262469793/1000000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((161523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c449 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((32921/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -755099/5000000) (δ := 14397/1000000000) (ψ := 487099/1000000) 286 278
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t449 : ((15534486893/400000000000 : ℚ) : ℝ) ≤ stT286 449 := by
  have hc : ((32917/40000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15534486893/400000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((32917/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c450 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((499741/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40231/5000000) (δ := 7203/500000000) (ψ := 487099/1000000) 286 278
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t450 : ((58889084041/1250000000000 : ℚ) : ℝ) ≤ stT286 450 := by
  have hc : ((499691/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).1
  have hw2 : ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58889084041/1250000000000 : ℚ) : ℝ)
      = ((117851/2500000 : ℚ) : ℝ) * ((499691/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c451 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((196413/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1667619/10000000) (δ := 7203/500000000) (ψ := 487099/1000000) 286 278
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t451 : ((23118844457/625000000000 : ℚ) : ℝ) ≤ stT286 451 := by
  have hc : ((49097/62500 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).1
  have hw2 : ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((470881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23118844457/625000000000 : ℚ) : ℝ)
      = ((470881/10000000 : ℚ) : ℝ) * ((49097/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c452 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((66759/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3251201/10000000) (δ := 7203/500000000) (ψ := 487099/1000000) 286 278
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t452 : ((392362553/31250000000 : ℚ) : ℝ) ≤ stT286 452 := by
  have hc : ((33367/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).1
  have hw2 : ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((392362553/31250000000 : ℚ) : ℝ)
      = ((11759/250000 : ℚ) : ℝ) * ((33367/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c453 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-176953/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4831351/10000000) (δ := 7203/500000000) (ψ := 487099/1000000) 286 278
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t453 : ((-83163266523/5000000000000 : ℚ) : ℝ) ≤ stT286 453 := by
  have hc : ((-177003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83163266523/5000000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-177003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c454 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-418663/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3203963/5000000) (δ := 7203/500000000) (ψ := 487099/1000000) 286 278
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t454 : ((-49128015003/1250000000000 : ℚ) : ℝ) ≤ stT286 454 := by
  have hc : ((-418713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49128015003/1250000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-418713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c455 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-998707/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7726823/10000000) (δ := 7249/500000000) (ψ := 487099/1000000) 286 279
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t455 : ((-58531089007/1250000000000 : ℚ) : ℝ) ≤ stT286 455 := by
  have hc : ((-998807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58531089007/1250000000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-998807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c456 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-778359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -769639/1250000) (δ := 7249/500000000) (ψ := 487099/1000000) 286 279
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t456 : ((-364546900487/10000000000000 : ℚ) : ℝ) ≤ stT286 456 := by
  have hc : ((-778459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-364546900487/10000000000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-778459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c457 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-52491/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -573863/1250000) (δ := 2861/200000000) (ψ := 487099/1000000) 286 279
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t457 : ((-24563648091/2000000000000 : ℚ) : ℝ) ≤ stT286 457 := by
  have hc : ((-52511/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).2
  have h0 : (0:ℝ) ≤ ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24563648091/2000000000000 : ℚ) : ℝ)
      = ((467781/10000000 : ℚ) : ℝ) * ((-52511/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c458 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((563/1600 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3028057/10000000) (δ := 2861/200000000) (ψ := 487099/1000000) 286 279
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t458 : ((6574942099/400000000000 : ℚ) : ℝ) ≤ stT286 458 := by
  have hc : ((14071/40000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).1
  have hw2 : ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((467269/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6574942099/400000000000 : ℚ) : ℝ)
      = ((467269/10000000 : ℚ) : ℝ) * ((14071/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c459 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((832369/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1468571/10000000) (δ := 7249/500000000) (ψ := 487099/1000000) 286 279
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t459 : ((9711746961/250000000000 : ℚ) : ℝ) ≤ stT286 459 := by
  have hc : ((832269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).1
  have hw2 : ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11669/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9711746961/250000000000 : ℚ) : ℝ)
      = ((11669/250000 : ℚ) : ℝ) * ((832269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c460 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((999389/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21853/2500000) (δ := 7249/500000000) (ψ := 487099/1000000) 286 279
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t460 : ((116480123707/2500000000000 : ℚ) : ℝ) ≤ stT286 460 := by
  have hc : ((999289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116480123707/2500000000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((999289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c461 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((792413/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 820053/5000000) (δ := 7249/500000000) (ψ := 487099/1000000) 286 279
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t461 : ((184508305249/5000000000000 : ℚ) : ℝ) ≤ stT286 461 := by
  have hc : ((792313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184508305249/5000000000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((792313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c462 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((290787/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 398671/1250000) (δ := 7249/500000000) (ψ := 487099/1000000) 286 279
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t462 : ((67619900627/5000000000000 : ℚ) : ℝ) ≤ stT286 462 := by
  have hc : ((290687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67619900627/5000000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((290687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c463 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-63547/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4735341/10000000) (δ := 7249/500000000) (ψ := 487099/1000000) 286 279
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t463 : ((-1477106379/100000000000 : ℚ) : ℝ) ≤ stT286 463 := by
  have hc : ((-63567/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).2
  have h0 : (0:ℝ) ≤ ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1477106379/100000000000 : ℚ) : ℝ)
      = ((23237/500000 : ℚ) : ℝ) * ((-63567/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c464 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-161557/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3138977/5000000) (δ := 2861/200000000) (ψ := 487099/1000000) 286 279
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t464 : ((-75010344903/2000000000000 : ℚ) : ℝ) ≤ stT286 464 := by
  have hc : ((-161577/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).2
  have h0 : (0:ℝ) ≤ ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75010344903/2000000000000 : ℚ) : ℝ)
      = ((464239/10000000 : ℚ) : ℝ) * ((-161577/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c465 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-249973/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7817277/10000000) (δ := 7249/500000000) (ψ := 487099/1000000) 286 279
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t465 : ((-57966911261/1250000000000 : ℚ) : ℝ) ≤ stT286 465 := by
  have hc : ((-124999/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).2
  have h0 : (0:ℝ) ≤ ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57966911261/1250000000000 : ℚ) : ℝ)
      = ((463739/10000000 : ℚ) : ℝ) * ((-124999/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c466 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-825503/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6354723/10000000) (δ := 14391/1000000000) (ψ := 487099/1000000) 286 280
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t466 : ((-191226992463/5000000000000 : ℚ) : ℝ) ≤ stT286 466 := by
  have hc : ((-825603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).2
  have h0 : (0:ℝ) ≤ ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191226992463/5000000000000 : ℚ) : ℝ)
      = ((231621/5000000 : ℚ) : ℝ) * ((-825603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c467 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-43803/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4822049/10000000) (δ := 14391/1000000000) (ψ := 487099/1000000) 286 280
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t467 : ((-8110161419/500000000000 : ℚ) : ℝ) ≤ stT286 467 := by
  have hc : ((-87631/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8110161419/500000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-87631/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c468 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((251017/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -411583/1250000) (δ := 14391/1000000000) (ψ := 487099/1000000) 286 280
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t468 : ((463945533/40000000000 : ℚ) : ℝ) ≤ stT286 468 := by
  have hc : ((250917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).1
  have hw2 : ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((463945533/40000000000 : ℚ) : ℝ)
      = ((1849/40000 : ℚ) : ℝ) * ((250917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c469 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((30423/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55203/312500) (δ := 3603/250000000) (ψ := 487099/1000000) 286 280
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t469 : ((14046186183/400000000000 : ℚ) : ℝ) ≤ stT286 469 := by
  have hc : ((30419/40000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).1
  have hw2 : ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((461757/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14046186183/400000000000 : ℚ) : ℝ)
      = ((461757/10000000 : ℚ) : ℝ) * ((30419/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c470 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((124407/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -121809/5000000) (δ := 14391/1000000000) (ψ := 487099/1000000) 286 280
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t470 : ((22951531617/500000000000 : ℚ) : ℝ) ≤ stT286 470 := by
  have hc : ((248789/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).1
  have hw2 : ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((92253/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22951531617/500000000000 : ℚ) : ℝ)
      = ((92253/2000000 : ℚ) : ℝ) * ((248789/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c471 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((872541/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1276043/10000000) (δ := 14391/1000000000) (ψ := 487099/1000000) 286 280
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t471 : ((16079960071/400000000000 : ℚ) : ℝ) ≤ stT286 471 := by
  have hc : ((872441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).1
  have hw2 : ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18431/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16079960071/400000000000 : ℚ) : ℝ)
      = ((18431/400000 : ℚ) : ℝ) * ((872441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c472 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((87677/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2792487/10000000) (δ := 3603/250000000) (ψ := 487099/1000000) 286 280
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t472 : ((40347377559/2000000000000 : ℚ) : ℝ) ≤ stT286 472 := by
  have hc : ((87657/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40347377559/2000000000000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((87657/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c473 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-15091/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4305713/10000000) (δ := 3603/250000000) (ψ := 487099/1000000) 286 280
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t473 : ((-6943454901/1000000000000 : ℚ) : ℝ) ≤ stT286 473 := by
  have hc : ((-15101/100000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).2
  have h0 : (0:ℝ) ≤ ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6943454901/1000000000000 : ℚ) : ℝ)
      = ((459801/10000000 : ℚ) : ℝ) * ((-15101/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c474 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-171417/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5815793/10000000) (δ := 3603/250000000) (ψ := 487099/1000000) 286 280
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t474 : ((-9843256709/312500000000 : ℚ) : ℝ) ≤ stT286 474 := by
  have hc : ((-85721/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).2
  have h0 : (0:ℝ) ≤ ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9843256709/312500000000 : ℚ) : ℝ)
      = ((114829/2500000 : ℚ) : ℝ) * ((-85721/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c475 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-391/400 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1464531/2000000) (δ := 14391/1000000000) (ψ := 487099/1000000) 286 280
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t475 : ((-17521647/390625000 : ℚ) : ℝ) ≤ stT286 475 := by
  have hc : ((-611/625 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).2
  have h0 : (0:ℝ) ≤ ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17521647/390625000 : ℚ) : ℝ)
      = ((28677/625000 : ℚ) : ℝ) * ((-611/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c476 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-231329/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6881663/10000000) (δ := 14319/1000000000) (ψ := 487099/1000000) 286 281
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t476 : ((-1060411059/25000000000 : ℚ) : ℝ) ≤ stT286 476 := by
  have hc : ((-115677/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).2
  have h0 : (0:ℝ) ≤ ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1060411059/25000000000 : ℚ) : ℝ)
      = ((9167/200000 : ℚ) : ℝ) * ((-115677/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c477 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-549419/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1345291/2500000) (δ := 14319/1000000000) (ψ := 487099/1000000) 286 281
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t477 : ((-251607715011/10000000000000 : ℚ) : ℝ) ≤ stT286 477 := by
  have hc : ((-549519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).2
  have h0 : (0:ℝ) ≤ ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251607715011/10000000000000 : ℚ) : ℝ)
      = ((457869/10000000 : ℚ) : ℝ) * ((-549519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c478 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((17299/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -194187/500000) (δ := 3621/250000000) (ψ := 487099/1000000) 286 281
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t478 : ((7866633411/10000000000000 : ℚ) : ℝ) ≤ stT286 478 := by
  have hc : ((17199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).1
  have hw2 : ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((457389/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7866633411/10000000000000 : ℚ) : ℝ)
      = ((457389/10000000 : ℚ) : ℝ) * ((17199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c479 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((115389/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2389533/10000000) (δ := 3621/250000000) (ψ := 487099/1000000) 286 281
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t479 : ((52713365159/2000000000000 : ℚ) : ℝ) ≤ stT286 479 := by
  have hc : ((115369/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).1
  have hw2 : ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((456911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52713365159/2000000000000 : ℚ) : ℝ)
      = ((456911/10000000 : ℚ) : ℝ) * ((115369/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c480 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((234033/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -898329/10000000) (δ := 3621/250000000) (ψ := 487099/1000000) 286 281
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t480 : ((2670236037/62500000000 : ℚ) : ℝ) ≤ stT286 480 := by
  have hc : ((29251/31250 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).1
  have hw2 : ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2670236037/62500000000 : ℚ) : ℝ)
      = ((91287/2000000 : ℚ) : ℝ) * ((29251/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c481 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((972313/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 294829/5000000) (δ := 14319/1000000000) (ψ := 487099/1000000) 286 281
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t481 : ((11082255987/250000000000 : ℚ) : ℝ) ≤ stT286 481 := by
  have hc : ((972213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).1
  have hw2 : ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11399/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11082255987/250000000000 : ℚ) : ℝ)
      = ((11399/250000 : ℚ) : ℝ) * ((972213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c482 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((337491/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2074641/10000000) (δ := 3621/250000000) (ψ := 487099/1000000) 286 281
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t482 : ((153699988767/5000000000000 : ℚ) : ℝ) ≤ stT286 482 := by
  have hc : ((337441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).1
  have hw2 : ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((455487/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153699988767/5000000000000 : ℚ) : ℝ)
      = ((455487/10000000 : ℚ) : ℝ) * ((337441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c483 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((147663/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3556479/10000000) (δ := 14319/1000000000) (ψ := 487099/1000000) 286 281
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t483 : ((13428675689/2000000000000 : ℚ) : ℝ) ≤ stT286 483 := by
  have hc : ((147563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13428675689/2000000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((147563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c484 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-428949/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5035313/10000000) (δ := 3621/250000000) (ψ := 487099/1000000) 286 281
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t484 : ((-97511253377/5000000000000 : ℚ) : ℝ) ≤ stT286 484 := by
  have hc : ((-429049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).2
  have h0 : (0:ℝ) ≤ ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97511253377/5000000000000 : ℚ) : ℝ)
      = ((227273/5000000 : ℚ) : ℝ) * ((-429049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c485 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-859149/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3255501/5000000) (δ := 14319/1000000000) (ψ := 487099/1000000) 286 281
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t485 : ((-390165208173/10000000000000 : ℚ) : ℝ) ≤ stT286 485 := by
  have hc : ((-859249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).2
  have h0 : (0:ℝ) ≤ ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-390165208173/10000000000000 : ℚ) : ℝ)
      = ((454077/10000000 : ℚ) : ℝ) * ((-859249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c486 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-998653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1931051/2500000) (δ := 7213/500000000) (ψ := 487099/1000000) 286 282
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t486 : ((-45304434833/1000000000000 : ℚ) : ℝ) ≤ stT286 486 := by
  have hc : ((-998753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).2
  have h0 : (0:ℝ) ≤ ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45304434833/1000000000000 : ℚ) : ℝ)
      = ((45361/1000000 : ℚ) : ℝ) * ((-998753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c487 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-32089/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3127261/5000000) (δ := 14377/1000000000) (ψ := 487099/1000000) 286 282
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t487 : ((-1817843799/50000000000 : ℚ) : ℝ) ≤ stT286 487 := by
  have hc : ((-32093/40000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).2
  have h0 : (0:ℝ) ≤ ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1817843799/50000000000 : ℚ) : ℝ)
      = ((56643/1250000 : ℚ) : ℝ) * ((-32093/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c488 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-42197/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2393921/5000000) (δ := 7213/500000000) (ψ := 487099/1000000) 286 282
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t488 : ((-38214708501/2500000000000 : ℚ) : ℝ) ≤ stT286 488 := by
  have hc : ((-84419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38214708501/2500000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-84419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c489 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((59693/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3324237/10000000) (δ := 7213/500000000) (ψ := 487099/1000000) 286 282
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t489 : ((1349138231/125000000000 : ℚ) : ℝ) ≤ stT286 489 := by
  have hc : ((14917/62500 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).1
  have hw2 : ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90443/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1349138231/125000000000 : ℚ) : ℝ)
      = ((90443/2000000 : ℚ) : ℝ) * ((14917/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c490 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((734799/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -465891/2500000) (δ := 14377/1000000000) (ψ := 487099/1000000) 286 282
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t490 : ((331902477347/10000000000000 : ℚ) : ℝ) ≤ stT286 490 := by
  have hc : ((734699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).1
  have hw2 : ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451753/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((331902477347/10000000000000 : ℚ) : ℝ)
      = ((451753/10000000 : ℚ) : ℝ) * ((734699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c491 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((493427/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -202911/5000000) (δ := 14377/1000000000) (ψ := 487099/1000000) 286 282
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t491 : ((222657586461/5000000000000 : ℚ) : ℝ) ≤ stT286 491 := by
  have hc : ((493377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).1
  have hw2 : ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451293/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222657586461/5000000000000 : ℚ) : ℝ)
      = ((451293/10000000 : ℚ) : ℝ) * ((493377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c492 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((182653/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1048917/10000000) (δ := 14377/1000000000) (ψ := 487099/1000000) 286 282
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t492 : ((41168582961/1000000000000 : ℚ) : ℝ) ≤ stT286 492 := by
  have hc : ((182633/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41168582961/1000000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((182633/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c493 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((270041/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2500653/10000000) (δ := 14377/1000000000) (ψ := 487099/1000000) 286 282
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t493 : ((121597736607/5000000000000 : ℚ) : ℝ) ≤ stT286 493 := by
  have hc : ((269991/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121597736607/5000000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((269991/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c494 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-1803/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3949529/10000000) (δ := 14377/1000000000) (ψ := 487099/1000000) 286 282
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t494 : ((-410103903/1000000000000 : ℚ) : ℝ) ≤ stT286 494 := by
  have hc : ((-1823/200000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).2
  have h0 : (0:ℝ) ≤ ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-410103903/1000000000000 : ℚ) : ℝ)
      = ((224961/5000000 : ℚ) : ℝ) * ((-1823/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c495 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-554169/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2697701/5000000) (δ := 14377/1000000000) (ψ := 487099/1000000) 286 282
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t495 : ((-249125624623/10000000000000 : ℚ) : ℝ) ≤ stT286 495 := by
  have hc : ((-554269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).2
  have h0 : (0:ℝ) ≤ ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-249125624623/10000000000000 : ℚ) : ℝ)
      = ((449467/10000000 : ℚ) : ℝ) * ((-554269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c496 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-459309/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1367683/2000000) (δ := 14377/1000000000) (ψ := 487099/1000000) 286 282
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t496 : ((-103129311013/2500000000000 : ℚ) : ℝ) ≤ stT286 496 := by
  have hc : ((-459359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).2
  have h0 : (0:ℝ) ≤ ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103129311013/2500000000000 : ℚ) : ℝ)
      = ((224507/5000000 : ℚ) : ℝ) * ((-459359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c497 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-492809/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7429467/10000000) (δ := 1447/100000000) (ψ := 487099/1000000) 286 283
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t497 : ((-110538909379/2500000000000 : ℚ) : ℝ) ≤ stT286 497 := by
  have hc : ((-492859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110538909379/2500000000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-492859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c498 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-367657/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5992317/10000000) (δ := 1447/100000000) (ψ := 487099/1000000) 286 283
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t498 : ((-164773551477/5000000000000 : ℚ) : ℝ) ≤ stT286 498 := by
  have hc : ((-367707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164773551477/5000000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-367707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c499 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-249743/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4558027/10000000) (δ := 1447/100000000) (ψ := 487099/1000000) 286 283
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t499 : ((-55922608533/5000000000000 : ℚ) : ℝ) ≤ stT286 499 := by
  have hc : ((-249843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55922608533/5000000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-249843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_c500 :
    |Real.cos (((286 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((78679/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3126597/10000000) (δ := 1447/100000000) (ψ := 487099/1000000) 286 283
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st286_t500 : ((17587545651/1250000000000 : ℚ) : ℝ) ≤ stT286 500 := by
  have hc : ((39327/125000 : ℚ) : ℝ)
      ≤ Real.cos (((286 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st286_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).1
  have hw2 : ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17587545651/1250000000000 : ℚ) : ℝ)
      = ((447213/10000000 : ℚ) : ℝ) * ((39327/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st286_p1 : ((441797/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT286 (i+1) := by
  rw [Finset.sum_range_one]
  exact st286_t1

theorem st286_p2 : ((465738696057/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT286 (i+1))
      = (∑ i ∈ Finset.range 1, stT286 (i+1)) + stT286 2 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 1
    simpa using h
  have hprev := st286_p1
  have hstep := st286_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p3 : ((442369790859/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT286 (i+1))
      = (∑ i ∈ Finset.range 2, stT286 (i+1)) + stT286 3 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 2
    simpa using h
  have hprev := st286_p2
  have hstep := st286_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p4 : ((751216040859/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT286 (i+1))
      = (∑ i ∈ Finset.range 3, stT286 (i+1)) + stT286 4 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 3
    simpa using h
  have hprev := st286_p3
  have hstep := st286_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p5 : ((13888062237199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT286 (i+1))
      = (∑ i ∈ Finset.range 4, stT286 (i+1)) + stT286 5 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 4
    simpa using h
  have hprev := st286_p4
  have hstep := st286_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p6 : ((9836263179427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT286 (i+1))
      = (∑ i ∈ Finset.range 5, stT286 (i+1)) + stT286 6 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 5
    simpa using h
  have hprev := st286_p5
  have hstep := st286_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p7 : ((3028450826401/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT286 (i+1))
      = (∑ i ∈ Finset.range 6, stT286 (i+1)) + stT286 7 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 6
    simpa using h
  have hprev := st286_p6
  have hstep := st286_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p8 : ((1453932579307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT286 (i+1))
      = (∑ i ∈ Finset.range 7, stT286 (i+1)) + stT286 8 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 7
    simpa using h
  have hprev := st286_p7
  have hstep := st286_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p9 : ((5978501518217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT286 (i+1))
      = (∑ i ∈ Finset.range 8, stT286 (i+1)) + stT286 9 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 8
    simpa using h
  have hprev := st286_p8
  have hstep := st286_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p10 : ((5626524165427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT286 (i+1))
      = (∑ i ∈ Finset.range 9, stT286 (i+1)) + stT286 10 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 9
    simpa using h
  have hprev := st286_p9
  have hstep := st286_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p11 : ((834932497519/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT286 (i+1))
      = (∑ i ∈ Finset.range 10, stT286 (i+1)) + stT286 11 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 10
    simpa using h
  have hprev := st286_p10
  have hstep := st286_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p12 : ((1397545931799/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT286 (i+1))
      = (∑ i ∈ Finset.range 11, stT286 (i+1)) + stT286 12 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 11
    simpa using h
  have hprev := st286_p11
  have hstep := st286_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p13 : ((1983087487763/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT286 (i+1))
      = (∑ i ∈ Finset.range 12, stT286 (i+1)) + stT286 13 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 12
    simpa using h
  have hprev := st286_p12
  have hstep := st286_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p14 : ((12467570762467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT286 (i+1))
      = (∑ i ∈ Finset.range 13, stT286 (i+1)) + stT286 14 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 13
    simpa using h
  have hprev := st286_p13
  have hstep := st286_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p15 : ((13442542341207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT286 (i+1))
      = (∑ i ∈ Finset.range 14, stT286 (i+1)) + stT286 15 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 14
    simpa using h
  have hprev := st286_p14
  have hstep := st286_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p16 : ((15198467341207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT286 (i+1))
      = (∑ i ∈ Finset.range 15, stT286 (i+1)) + stT286 16 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 15
    simpa using h
  have hprev := st286_p15
  have hstep := st286_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p17 : ((17023242136351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT286 (i+1))
      = (∑ i ∈ Finset.range 16, stT286 (i+1)) + stT286 17 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 16
    simpa using h
  have hprev := st286_p16
  have hstep := st286_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p18 : ((14673455196961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT286 (i+1))
      = (∑ i ∈ Finset.range 17, stT286 (i+1)) + stT286 18 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 17
    simpa using h
  have hprev := st286_p17
  have hstep := st286_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p19 : ((8423865511463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT286 (i+1))
      = (∑ i ∈ Finset.range 18, stT286 (i+1)) + stT286 19 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 18
    simpa using h
  have hprev := st286_p18
  have hstep := st286_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p20 : ((8192518562081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT286 (i+1))
      = (∑ i ∈ Finset.range 19, stT286 (i+1)) + stT286 20 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 19
    simpa using h
  have hprev := st286_p19
  have hstep := st286_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p21 : ((7101664737413/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT286 (i+1))
      = (∑ i ∈ Finset.range 20, stT286 (i+1)) + stT286 21 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 20
    simpa using h
  have hprev := st286_p20
  have hstep := st286_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p22 : ((6331459791349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT286 (i+1))
      = (∑ i ∈ Finset.range 21, stT286 (i+1)) + stT286 22 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 21
    simpa using h
  have hprev := st286_p21
  have hstep := st286_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p23 : ((11383539250193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT286 (i+1))
      = (∑ i ∈ Finset.range 22, stT286 (i+1)) + stT286 23 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 22
    simpa using h
  have hprev := st286_p22
  have hstep := st286_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p24 : ((9607889370539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT286 (i+1))
      = (∑ i ∈ Finset.range 23, stT286 (i+1)) + stT286 24 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 23
    simpa using h
  have hprev := st286_p23
  have hstep := st286_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p25 : ((968357305003/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT286 (i+1))
      = (∑ i ∈ Finset.range 24, stT286 (i+1)) + stT286 25 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 24
    simpa using h
  have hprev := st286_p24
  have hstep := st286_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p26 : ((8046921956507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT286 (i+1))
      = (∑ i ∈ Finset.range 25, stT286 (i+1)) + stT286 26 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 25
    simpa using h
  have hprev := st286_p25
  have hstep := st286_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p27 : ((9850857805007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT286 (i+1))
      = (∑ i ∈ Finset.range 26, stT286 (i+1)) + stT286 27 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 26
    simpa using h
  have hprev := st286_p26
  have hstep := st286_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p28 : ((1039186557997/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT286 (i+1))
      = (∑ i ∈ Finset.range 27, stT286 (i+1)) + stT286 28 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 27
    simpa using h
  have hprev := st286_p27
  have hstep := st286_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p29 : ((8930184698323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT286 (i+1))
      = (∑ i ∈ Finset.range 28, stT286 (i+1)) + stT286 29 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 28
    simpa using h
  have hprev := st286_p28
  have hstep := st286_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p30 : ((8806706115379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT286 (i+1))
      = (∑ i ∈ Finset.range 29, stT286 (i+1)) + stT286 30 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 29
    simpa using h
  have hprev := st286_p29
  have hstep := st286_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p31 : ((9011635762679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT286 (i+1))
      = (∑ i ∈ Finset.range 30, stT286 (i+1)) + stT286 31 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 30
    simpa using h
  have hprev := st286_p30
  have hstep := st286_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p32 : ((1028511118729/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT286 (i+1))
      = (∑ i ∈ Finset.range 31, stT286 (i+1)) + stT286 32 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 31
    simpa using h
  have hprev := st286_p31
  have hstep := st286_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p33 : ((1220728039843/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT286 (i+1))
      = (∑ i ∈ Finset.range 32, stT286 (i+1)) + stT286 33 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 32
    simpa using h
  have hprev := st286_p32
  have hstep := st286_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p34 : ((4092764087113/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT286 (i+1))
      = (∑ i ∈ Finset.range 33, stT286 (i+1)) + stT286 34 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 33
    simpa using h
  have hprev := st286_p33
  have hstep := st286_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p35 : ((4124128597207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT286 (i+1))
      = (∑ i ∈ Finset.range 34, stT286 (i+1)) + stT286 35 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 34
    simpa using h
  have hprev := st286_p34
  have hstep := st286_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p36 : ((4933469940137/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT286 (i+1))
      = (∑ i ∈ Finset.range 35, stT286 (i+1)) + stT286 36 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 35
    simpa using h
  have hprev := st286_p35
  have hstep := st286_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p37 : ((297012571047/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT286 (i+1))
      = (∑ i ∈ Finset.range 36, stT286 (i+1)) + stT286 37 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 36
    simpa using h
  have hprev := st286_p36
  have hstep := st286_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p38 : ((7882042896369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT286 (i+1))
      = (∑ i ∈ Finset.range 37, stT286 (i+1)) + stT286 38 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 37
    simpa using h
  have hprev := st286_p37
  have hstep := st286_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p39 : ((7214911985683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT286 (i+1))
      = (∑ i ∈ Finset.range 38, stT286 (i+1)) + stT286 39 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 38
    simpa using h
  have hprev := st286_p38
  have hstep := st286_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p40 : ((8011462430737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT286 (i+1))
      = (∑ i ∈ Finset.range 39, stT286 (i+1)) + stT286 40 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 39
    simpa using h
  have hprev := st286_p39
  have hstep := st286_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p41 : ((1903802680757/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT286 (i+1))
      = (∑ i ∈ Finset.range 40, stT286 (i+1)) + stT286 41 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 40
    simpa using h
  have hprev := st286_p40
  have hstep := st286_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p42 : ((2742753021471/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT286 (i+1))
      = (∑ i ∈ Finset.range 41, stT286 (i+1)) + stT286 42 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 41
    simpa using h
  have hprev := st286_p41
  have hstep := st286_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p43 : ((6021317147617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT286 (i+1))
      = (∑ i ∈ Finset.range 42, stT286 (i+1)) + stT286 43 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 42
    simpa using h
  have hprev := st286_p42
  have hstep := st286_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p44 : ((6374344551249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT286 (i+1))
      = (∑ i ∈ Finset.range 43, stT286 (i+1)) + stT286 44 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 43
    simpa using h
  have hprev := st286_p43
  have hstep := st286_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p45 : ((3312644675139/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT286 (i+1))
      = (∑ i ∈ Finset.range 44, stT286 (i+1)) + stT286 45 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 44
    simpa using h
  have hprev := st286_p44
  have hstep := st286_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p46 : ((13743121637277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT286 (i+1))
      = (∑ i ∈ Finset.range 45, stT286 (i+1)) + stT286 46 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 45
    simpa using h
  have hprev := st286_p45
  have hstep := st286_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p47 : ((7203800947991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT286 (i+1))
      = (∑ i ∈ Finset.range 46, stT286 (i+1)) + stT286 47 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 46
    simpa using h
  have hprev := st286_p46
  have hstep := st286_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p48 : ((960961010827/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT286 (i+1))
      = (∑ i ∈ Finset.range 47, stT286 (i+1)) + stT286 48 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 47
    simpa using h
  have hprev := st286_p47
  have hstep := st286_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p49 : ((16661777215883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT286 (i+1))
      = (∑ i ∈ Finset.range 48, stT286 (i+1)) + stT286 49 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 48
    simpa using h
  have hprev := st286_p48
  have hstep := st286_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p50 : ((2259209040097/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT286 (i+1))
      = (∑ i ∈ Finset.range 49, stT286 (i+1)) + stT286 50 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 49
    simpa using h
  have hprev := st286_p49
  have hstep := st286_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p51 : ((2395828058437/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT286 (i+1))
      = (∑ i ∈ Finset.range 50, stT286 (i+1)) + stT286 51 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 50
    simpa using h
  have hprev := st286_p50
  have hstep := st286_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p52 : ((9697852930123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT286 (i+1))
      = (∑ i ∈ Finset.range 51, stT286 (i+1)) + stT286 52 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 51
    simpa using h
  have hprev := st286_p51
  have hstep := st286_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p53 : ((2317910383001/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT286 (i+1))
      = (∑ i ∈ Finset.range 52, stT286 (i+1)) + stT286 53 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 52
    simpa using h
  have hprev := st286_p52
  have hstep := st286_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p54 : ((4295797817989/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT286 (i+1))
      = (∑ i ∈ Finset.range 53, stT286 (i+1)) + stT286 54 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 53
    simpa using h
  have hprev := st286_p53
  have hstep := st286_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p55 : ((4134250396289/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT286 (i+1))
      = (∑ i ∈ Finset.range 54, stT286 (i+1)) + stT286 55 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 54
    simpa using h
  have hprev := st286_p54
  have hstep := st286_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p56 : ((433109962869/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT286 (i+1))
      = (∑ i ∈ Finset.range 55, stT286 (i+1)) + stT286 56 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 55
    simpa using h
  have hprev := st286_p55
  have hstep := st286_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p57 : ((4649254533021/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT286 (i+1))
      = (∑ i ∈ Finset.range 56, stT286 (i+1)) + stT286 57 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 56
    simpa using h
  have hprev := st286_p56
  have hstep := st286_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p58 : ((18572107975969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT286 (i+1))
      = (∑ i ∈ Finset.range 57, stT286 (i+1)) + stT286 58 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 57
    simpa using h
  have hprev := st286_p57
  have hstep := st286_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p59 : ((17286250751319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT286 (i+1))
      = (∑ i ∈ Finset.range 58, stT286 (i+1)) + stT286 59 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 58
    simpa using h
  have hprev := st286_p58
  have hstep := st286_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p60 : ((8481999517197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT286 (i+1))
      = (∑ i ∈ Finset.range 59, stT286 (i+1)) + stT286 60 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 59
    simpa using h
  have hprev := st286_p59
  have hstep := st286_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p61 : ((1819881410169/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT286 (i+1))
      = (∑ i ∈ Finset.range 60, stT286 (i+1)) + stT286 61 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 60
    simpa using h
  have hprev := st286_p60
  have hstep := st286_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p62 : ((3691514091087/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT286 (i+1))
      = (∑ i ∈ Finset.range 61, stT286 (i+1)) + stT286 62 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 61
    simpa using h
  have hprev := st286_p61
  have hstep := st286_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p63 : ((3440112197279/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT286 (i+1))
      = (∑ i ∈ Finset.range 62, stT286 (i+1)) + stT286 63 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 62
    simpa using h
  have hprev := st286_p62
  have hstep := st286_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p64 : ((3474815947279/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT286 (i+1))
      = (∑ i ∈ Finset.range 63, stT286 (i+1)) + stT286 64 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 63
    simpa using h
  have hprev := st286_p63
  have hstep := st286_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p65 : ((18507737048843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT286 (i+1))
      = (∑ i ∈ Finset.range 64, stT286 (i+1)) + stT286 65 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 64
    simpa using h
  have hprev := st286_p64
  have hstep := st286_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p66 : ((4414137062027/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT286 (i+1))
      = (∑ i ∈ Finset.range 65, stT286 (i+1)) + stT286 66 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 65
    simpa using h
  have hprev := st286_p65
  have hstep := st286_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p67 : ((17185395462883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT286 (i+1))
      = (∑ i ∈ Finset.range 66, stT286 (i+1)) + stT286 67 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 66
    simpa using h
  have hprev := st286_p66
  have hstep := st286_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p68 : ((18394126195993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT286 (i+1))
      = (∑ i ∈ Finset.range 67, stT286 (i+1)) + stT286 68 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 67
    simpa using h
  have hprev := st286_p67
  have hstep := st286_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p69 : ((4424465877153/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT286 (i+1))
      = (∑ i ∈ Finset.range 68, stT286 (i+1)) + stT286 69 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 68
    simpa using h
  have hprev := st286_p68
  have hstep := st286_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p70 : ((432001840053/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT286 (i+1))
      = (∑ i ∈ Finset.range 69, stT286 (i+1)) + stT286 70 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 69
    simpa using h
  have hprev := st286_p69
  have hstep := st286_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p71 : ((9207108058823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT286 (i+1))
      = (∑ i ∈ Finset.range 70, stT286 (i+1)) + stT286 71 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 70
    simpa using h
  have hprev := st286_p70
  have hstep := st286_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p72 : ((8707760739303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT286 (i+1))
      = (∑ i ∈ Finset.range 71, stT286 (i+1)) + stT286 72 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 71
    simpa using h
  have hprev := st286_p71
  have hstep := st286_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p73 : ((3531334358127/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT286 (i+1))
      = (∑ i ∈ Finset.range 72, stT286 (i+1)) + stT286 73 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 72
    simpa using h
  have hprev := st286_p72
  have hstep := st286_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p74 : ((3651240270099/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT286 (i+1))
      = (∑ i ∈ Finset.range 73, stT286 (i+1)) + stT286 74 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 73
    simpa using h
  have hprev := st286_p73
  have hstep := st286_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p75 : ((4291053906477/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT286 (i+1))
      = (∑ i ∈ Finset.range 74, stT286 (i+1)) + stT286 75 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 74
    simpa using h
  have hprev := st286_p74
  have hstep := st286_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p76 : ((9127345530999/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT286 (i+1))
      = (∑ i ∈ Finset.range 75, stT286 (i+1)) + stT286 76 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 75
    simpa using h
  have hprev := st286_p75
  have hstep := st286_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p77 : ((1755709492437/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT286 (i+1))
      = (∑ i ∈ Finset.range 76, stT286 (i+1)) + stT286 77 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 76
    simpa using h
  have hprev := st286_p76
  have hstep := st286_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p78 : ((2210139719161/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT286 (i+1))
      = (∑ i ∈ Finset.range 77, stT286 (i+1)) + stT286 78 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 77
    simpa using h
  have hprev := st286_p77
  have hstep := st286_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p79 : ((724429333973/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT286 (i+1))
      = (∑ i ∈ Finset.range 78, stT286 (i+1)) + stT286 79 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 78
    simpa using h
  have hprev := st286_p78
  have hstep := st286_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p80 : ((3454450514137/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT286 (i+1))
      = (∑ i ∈ Finset.range 79, stT286 (i+1)) + stT286 80 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 79
    simpa using h
  have hprev := st286_p79
  have hstep := st286_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p81 : ((18329710242717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT286 (i+1))
      = (∑ i ∈ Finset.range 80, stT286 (i+1)) + stT286 81 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 80
    simpa using h
  have hprev := st286_p80
  have hstep := st286_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p82 : ((17227012065657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT286 (i+1))
      = (∑ i ∈ Finset.range 81, stT286 (i+1)) + stT286 82 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 81
    simpa using h
  have hprev := st286_p81
  have hstep := st286_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p83 : ((18245802757303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT286 (i+1))
      = (∑ i ∈ Finset.range 82, stT286 (i+1)) + stT286 83 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 82
    simpa using h
  have hprev := st286_p82
  have hstep := st286_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p84 : ((17386871614233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT286 (i+1))
      = (∑ i ∈ Finset.range 83, stT286 (i+1)) + stT286 84 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 83
    simpa using h
  have hprev := st286_p83
  have hstep := st286_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p85 : ((18054408756461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT286 (i+1))
      = (∑ i ∈ Finset.range 84, stT286 (i+1)) + stT286 85 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 84
    simpa using h
  have hprev := st286_p84
  have hstep := st286_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p86 : ((17575960014501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT286 (i+1))
      = (∑ i ∈ Finset.range 85, stT286 (i+1)) + stT286 86 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 85
    simpa using h
  have hprev := st286_p85
  have hstep := st286_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p87 : ((17887334574773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT286 (i+1))
      = (∑ i ∈ Finset.range 86, stT286 (i+1)) + stT286 87 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 86
    simpa using h
  have hprev := st286_p86
  have hstep := st286_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p88 : ((17709226626453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT286 (i+1))
      = (∑ i ∈ Finset.range 87, stT286 (i+1)) + stT286 88 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 87
    simpa using h
  have hprev := st286_p87
  have hstep := st286_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p89 : ((17791401833881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT286 (i+1))
      = (∑ i ∈ Finset.range 88, stT286 (i+1)) + stT286 89 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 88
    simpa using h
  have hprev := st286_p88
  have hstep := st286_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p90 : ((2220785481473/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT286 (i+1))
      = (∑ i ∈ Finset.range 89, stT286 (i+1)) + stT286 90 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 89
    simpa using h
  have hprev := st286_p89
  have hstep := st286_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p91 : ((1110718101883/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT286 (i+1))
      = (∑ i ∈ Finset.range 90, stT286 (i+1)) + stT286 91 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 90
    simpa using h
  have hprev := st286_p90
  have hstep := st286_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p92 : ((17749544511051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT286 (i+1))
      = (∑ i ∈ Finset.range 91, stT286 (i+1)) + stT286 92 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 91
    simpa using h
  have hprev := st286_p91
  have hstep := st286_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p93 : ((1113913458573/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT286 (i+1))
      = (∑ i ∈ Finset.range 92, stT286 (i+1)) + stT286 93 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 92
    simpa using h
  have hprev := st286_p92
  have hstep := st286_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p94 : ((4416237526851/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT286 (i+1))
      = (∑ i ∈ Finset.range 93, stT286 (i+1)) + stT286 94 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 93
    simpa using h
  have hprev := st286_p93
  have hstep := st286_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p95 : ((8968499729931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT286 (i+1))
      = (∑ i ∈ Finset.range 94, stT286 (i+1)) + stT286 95 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 94
    simpa using h
  have hprev := st286_p94
  have hstep := st286_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p96 : ((438128400507/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT286 (i+1))
      = (∑ i ∈ Finset.range 95, stT286 (i+1)) + stT286 96 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 95
    simpa using h
  have hprev := st286_p95
  have hstep := st286_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p97 : ((9046276497133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT286 (i+1))
      = (∑ i ∈ Finset.range 96, stT286 (i+1)) + stT286 97 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 96
    simpa using h
  have hprev := st286_p96
  have hstep := st286_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p98 : ((4341717295149/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT286 (i+1))
      = (∑ i ∈ Finset.range 97, stT286 (i+1)) + stT286 98 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 97
    simpa using h
  have hprev := st286_p97
  have hstep := st286_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p99 : ((9116592471817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT286 (i+1))
      = (∑ i ∈ Finset.range 98, stT286 (i+1)) + stT286 99 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 98
    simpa using h
  have hprev := st286_p98
  have hstep := st286_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p100 : ((8633896971817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT286 (i+1))
      = (∑ i ∈ Finset.range 99, stT286 (i+1)) + stT286 100 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 99
    simpa using h
  have hprev := st286_p99
  have hstep := st286_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p101 : ((3652447381309/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT286 (i+1))
      = (∑ i ∈ Finset.range 100, stT286 (i+1)) + stT286 101 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 100
    simpa using h
  have hprev := st286_p100
  have hstep := st286_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p102 : ((17333857309229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT286 (i+1))
      = (∑ i ∈ Finset.range 101, stT286 (i+1)) + stT286 102 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 101
    simpa using h
  have hprev := st286_p101
  have hstep := st286_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p103 : ((18083097539513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT286 (i+1))
      = (∑ i ∈ Finset.range 102, stT286 (i+1)) + stT286 103 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 102
    simpa using h
  have hprev := st286_p102
  have hstep := st286_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p104 : ((2203145163701/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT286 (i+1))
      = (∑ i ∈ Finset.range 103, stT286 (i+1)) + stT286 104 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 103
    simpa using h
  have hprev := st286_p103
  have hstep := st286_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p105 : ((2213012000651/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT286 (i+1))
      = (∑ i ∈ Finset.range 104, stT286 (i+1)) + stT286 105 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 104
    simpa using h
  have hprev := st286_p104
  have hstep := st286_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p106 : ((9018348506449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT286 (i+1))
      = (∑ i ∈ Finset.range 105, stT286 (i+1)) + stT286 106 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 105
    simpa using h
  have hprev := st286_p105
  have hstep := st286_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p107 : ((17339262972251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT286 (i+1))
      = (∑ i ∈ Finset.range 106, stT286 (i+1)) + stT286 107 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 106
    simpa using h
  have hprev := st286_p106
  have hstep := st286_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p108 : ((18262879597001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT286 (i+1))
      = (∑ i ∈ Finset.range 107, stT286 (i+1)) + stT286 108 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 107
    simpa using h
  have hprev := st286_p107
  have hstep := st286_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p109 : ((17328394840991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT286 (i+1))
      = (∑ i ∈ Finset.range 108, stT286 (i+1)) + stT286 109 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 108
    simpa using h
  have hprev := st286_p108
  have hstep := st286_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p110 : ((18025042804753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT286 (i+1))
      = (∑ i ∈ Finset.range 109, stT286 (i+1)) + stT286 110 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 109
    simpa using h
  have hprev := st286_p109
  have hstep := st286_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p111 : ((3555069372107/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT286 (i+1))
      = (∑ i ∈ Finset.range 110, stT286 (i+1)) + stT286 111 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 110
    simpa using h
  have hprev := st286_p110
  have hstep := st286_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p112 : ((17486573249127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT286 (i+1))
      = (∑ i ∈ Finset.range 111, stT286 (i+1)) + stT286 112 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 111
    simpa using h
  have hprev := st286_p111
  have hstep := st286_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p113 : ((18229072256487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT286 (i+1))
      = (∑ i ∈ Finset.range 112, stT286 (i+1)) + stT286 113 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 112
    simpa using h
  have hprev := st286_p112
  have hstep := st286_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p114 : ((17293112832521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT286 (i+1))
      = (∑ i ∈ Finset.range 113, stT286 (i+1)) + stT286 114 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 113
    simpa using h
  have hprev := st286_p113
  have hstep := st286_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p115 : ((18060254965697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT286 (i+1))
      = (∑ i ∈ Finset.range 114, stT286 (i+1)) + stT286 115 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 114
    simpa using h
  have hprev := st286_p114
  have hstep := st286_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p116 : ((8892507229193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT286 (i+1))
      = (∑ i ∈ Finset.range 115, stT286 (i+1)) + stT286 116 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 115
    simpa using h
  have hprev := st286_p115
  have hstep := st286_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p117 : ((8718530933009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT286 (i+1))
      = (∑ i ∈ Finset.range 116, stT286 (i+1)) + stT286 117 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 116
    simpa using h
  have hprev := st286_p116
  have hstep := st286_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p118 : ((4563643711249/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT286 (i+1))
      = (∑ i ∈ Finset.range 117, stT286 (i+1)) + stT286 118 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 117
    simpa using h
  have hprev := st286_p117
  have hstep := st286_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p119 : ((17366417268361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT286 (i+1))
      = (∑ i ∈ Finset.range 118, stT286 (i+1)) + stT286 119 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 118
    simpa using h
  have hprev := st286_p118
  have hstep := st286_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p120 : ((17860430561911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT286 (i+1))
      = (∑ i ∈ Finset.range 119, stT286 (i+1)) + stT286 120 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 119
    simpa using h
  have hprev := st286_p119
  have hstep := st286_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p121 : ((18037556748421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT286 (i+1))
      = (∑ i ∈ Finset.range 120, stT286 (i+1)) + stT286 121 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 120
    simpa using h
  have hprev := st286_p120
  have hstep := st286_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p122 : ((17283625306069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT286 (i+1))
      = (∑ i ∈ Finset.range 121, stT286 (i+1)) + stT286 122 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 121
    simpa using h
  have hprev := st286_p121
  have hstep := st286_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p123 : ((1135217514247/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT286 (i+1))
      = (∑ i ∈ Finset.range 122, stT286 (i+1)) + stT286 123 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 122
    simpa using h
  have hprev := st286_p122
  have hstep := st286_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p124 : ((17713251697421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT286 (i+1))
      = (∑ i ∈ Finset.range 123, stT286 (i+1)) + stT286 124 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 123
    simpa using h
  have hprev := st286_p123
  have hstep := st286_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p125 : ((17432367317157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT286 (i+1))
      = (∑ i ∈ Finset.range 124, stT286 (i+1)) + stT286 125 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 124
    simpa using h
  have hprev := st286_p124
  have hstep := st286_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p126 : ((18256667947277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT286 (i+1))
      = (∑ i ∈ Finset.range 125, stT286 (i+1)) + stT286 126 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 125
    simpa using h
  have hprev := st286_p125
  have hstep := st286_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p127 : ((8737228270139/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT286 (i+1))
      = (∑ i ∈ Finset.range 126, stT286 (i+1)) + stT286 127 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 126
    simpa using h
  have hprev := st286_p126
  have hstep := st286_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p128 : ((3526590711191/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT286 (i+1))
      = (∑ i ∈ Finset.range 127, stT286 (i+1)) + stT286 128 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 127
    simpa using h
  have hprev := st286_p127
  have hstep := st286_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p129 : ((3644720511601/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT286 (i+1))
      = (∑ i ∈ Finset.range 128, stT286 (i+1)) + stT286 129 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 128
    simpa using h
  have hprev := st286_p128
  have hstep := st286_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p130 : ((17350646440007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT286 (i+1))
      = (∑ i ∈ Finset.range 129, stT286 (i+1)) + stT286 130 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 129
    simpa using h
  have hprev := st286_p129
  have hstep := st286_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p131 : ((3557391698187/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT286 (i+1))
      = (∑ i ∈ Finset.range 130, stT286 (i+1)) + stT286 131 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 130
    simpa using h
  have hprev := st286_p130
  have hstep := st286_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p132 : ((18160495945791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT286 (i+1))
      = (∑ i ∈ Finset.range 131, stT286 (i+1)) + stT286 132 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 131
    simpa using h
  have hprev := st286_p131
  have hstep := st286_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p133 : ((17302277291731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT286 (i+1))
      = (∑ i ∈ Finset.range 132, stT286 (i+1)) + stT286 133 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 132
    simpa using h
  have hprev := st286_p132
  have hstep := st286_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p134 : ((3573784227983/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT286 (i+1))
      = (∑ i ∈ Finset.range 133, stT286 (i+1)) + stT286 134 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 133
    simpa using h
  have hprev := st286_p133
  have hstep := st286_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p135 : ((18122882700889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT286 (i+1))
      = (∑ i ∈ Finset.range 134, stT286 (i+1)) + stT286 135 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 134
    simpa using h
  have hprev := st286_p134
  have hstep := st286_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p136 : ((17289937153/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT286 (i+1))
      = (∑ i ∈ Finset.range 135, stT286 (i+1)) + stT286 136 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 135
    simpa using h
  have hprev := st286_p135
  have hstep := st286_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p137 : ((14305092629/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT286 (i+1))
      = (∑ i ∈ Finset.range 136, stT286 (i+1)) + stT286 137 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 136
    simpa using h
  have hprev := st286_p136
  have hstep := st286_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p138 : ((9065144607257/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT286 (i+1))
      = (∑ i ∈ Finset.range 137, stT286 (i+1)) + stT286 138 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 137
    simpa using h
  have hprev := st286_p137
  have hstep := st286_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p139 : ((2162309843013/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT286 (i+1))
      = (∑ i ∈ Finset.range 138, stT286 (i+1)) + stT286 139 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 138
    simpa using h
  have hprev := st286_p138
  have hstep := st286_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p140 : ((4456919670609/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT286 (i+1))
      = (∑ i ∈ Finset.range 139, stT286 (i+1)) + stT286 140 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 139
    simpa using h
  have hprev := st286_p139
  have hstep := st286_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p141 : ((3635621058579/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT286 (i+1))
      = (∑ i ∈ Finset.range 140, stT286 (i+1)) + stT286 141 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 140
    simpa using h
  have hprev := st286_p140
  have hstep := st286_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p142 : ((17339027351463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT286 (i+1))
      = (∑ i ∈ Finset.range 141, stT286 (i+1)) + stT286 142 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 141
    simpa using h
  have hprev := st286_p141
  have hstep := st286_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p143 : ((3541646642383/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT286 (i+1))
      = (∑ i ∈ Finset.range 142, stT286 (i+1)) + stT286 143 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 142
    simpa using h
  have hprev := st286_p142
  have hstep := st286_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p144 : ((9119679416399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT286 (i+1))
      = (∑ i ∈ Finset.range 143, stT286 (i+1)) + stT286 144 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 143
    simpa using h
  have hprev := st286_p143
  have hstep := st286_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p145 : ((17441789020343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT286 (i+1))
      = (∑ i ∈ Finset.range 144, stT286 (i+1)) + stT286 145 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 144
    simpa using h
  have hprev := st286_p144
  have hstep := st286_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p146 : ((8767157215869/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT286 (i+1))
      = (∑ i ∈ Finset.range 145, stT286 (i+1)) + stT286 146 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 145
    simpa using h
  have hprev := st286_p145
  have hstep := st286_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p147 : ((2282573395889/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT286 (i+1))
      = (∑ i ∈ Finset.range 146, stT286 (i+1)) + stT286 147 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 146
    simpa using h
  have hprev := st286_p146
  have hstep := st286_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p148 : ((17636628024507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT286 (i+1))
      = (∑ i ∈ Finset.range 147, stT286 (i+1)) + stT286 148 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 147
    simpa using h
  have hprev := st286_p147
  have hstep := st286_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p149 : ((17352637155547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT286 (i+1))
      = (∑ i ∈ Finset.range 148, stT286 (i+1)) + stT286 149 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 148
    simpa using h
  have hprev := st286_p148
  have hstep := st286_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p150 : ((18168995984219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT286 (i+1))
      = (∑ i ∈ Finset.range 149, stT286 (i+1)) + stT286 150 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 149
    simpa using h
  have hprev := st286_p149
  have hstep := st286_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p151 : ((8957276323267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT286 (i+1))
      = (∑ i ∈ Finset.range 150, stT286 (i+1)) + stT286 151 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 150
    simpa using h
  have hprev := st286_p150
  have hstep := st286_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p152 : ((8630710453631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT286 (i+1))
      = (∑ i ∈ Finset.range 151, stT286 (i+1)) + stT286 152 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 151
    simpa using h
  have hprev := st286_p151
  have hstep := st286_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p153 : ((8956990362503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT286 (i+1))
      = (∑ i ∈ Finset.range 152, stT286 (i+1)) + stT286 153 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 152
    simpa using h
  have hprev := st286_p152
  have hstep := st286_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p154 : ((9090887357667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT286 (i+1))
      = (∑ i ∈ Finset.range 153, stT286 (i+1)) + stT286 154 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 153
    simpa using h
  have hprev := st286_p153
  have hstep := st286_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p155 : ((8689925154597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT286 (i+1))
      = (∑ i ∈ Finset.range 154, stT286 (i+1)) + stT286 155 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 154
    simpa using h
  have hprev := st286_p154
  have hstep := st286_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p156 : ((8773299400677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT286 (i+1))
      = (∑ i ∈ Finset.range 155, stT286 (i+1)) + stT286 156 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 155
    simpa using h
  have hprev := st286_p155
  have hstep := st286_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p157 : ((1825929438787/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT286 (i+1))
      = (∑ i ∈ Finset.range 156, stT286 (i+1)) + stT286 157 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 156
    simpa using h
  have hprev := st286_p156
  have hstep := st286_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p158 : ((8869818746693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT286 (i+1))
      = (∑ i ∈ Finset.range 157, stT286 (i+1)) + stT286 158 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 157
    simpa using h
  have hprev := st286_p157
  have hstep := st286_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p159 : ((8637614310671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT286 (i+1))
      = (∑ i ∈ Finset.range 158, stT286 (i+1)) + stT286 159 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 158
    simpa using h
  have hprev := st286_p158
  have hstep := st286_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p160 : ((9001163789873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT286 (i+1))
      = (∑ i ∈ Finset.range 159, stT286 (i+1)) + stT286 160 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 159
    simpa using h
  have hprev := st286_p159
  have hstep := st286_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p161 : ((4538170604359/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT286 (i+1))
      = (∑ i ∈ Finset.range 160, stT286 (i+1)) + stT286 161 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 160
    simpa using h
  have hprev := st286_p160
  have hstep := st286_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p162 : ((1085434624471/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT286 (i+1))
      = (∑ i ∈ Finset.range 161, stT286 (i+1)) + stT286 162 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 161
    simpa using h
  have hprev := st286_p161
  have hstep := st286_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p163 : ((34219520753/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT286 (i+1))
      = (∑ i ∈ Finset.range 162, stT286 (i+1)) + stT286 163 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 162
    simpa using h
  have hprev := st286_p162
  have hstep := st286_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p164 : ((2280839484033/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT286 (i+1))
      = (∑ i ∈ Finset.range 163, stT286 (i+1)) + stT286 164 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 163
    simpa using h
  have hprev := st286_p163
  have hstep := st286_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p165 : ((17844041157009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT286 (i+1))
      = (∑ i ∈ Finset.range 164, stT286 (i+1)) + stT286 165 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 164
    simpa using h
  have hprev := st286_p164
  have hstep := st286_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p166 : ((17250737361891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT286 (i+1))
      = (∑ i ∈ Finset.range 165, stT286 (i+1)) + stT286 166 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 165
    simpa using h
  have hprev := st286_p165
  have hstep := st286_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p167 : ((8915436619407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT286 (i+1))
      = (∑ i ∈ Finset.range 166, stT286 (i+1)) + stT286 167 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 166
    simpa using h
  have hprev := st286_p166
  have hstep := st286_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p168 : ((1825771523733/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT286 (i+1))
      = (∑ i ∈ Finset.range 167, stT286 (i+1)) + stT286 168 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 167
    simpa using h
  have hprev := st286_p167
  have hstep := st286_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p169 : ((87841536691/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT286 (i+1))
      = (∑ i ∈ Finset.range 168, stT286 (i+1)) + stT286 169 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 168
    simpa using h
  have hprev := st286_p168
  have hstep := st286_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p170 : ((432751678871/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT286 (i+1))
      = (∑ i ∈ Finset.range 169, stT286 (i+1)) + stT286 170 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 169
    simpa using h
  have hprev := st286_p169
  have hstep := st286_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p171 : ((902669465861/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT286 (i+1))
      = (∑ i ∈ Finset.range 170, stT286 (i+1)) + stT286 171 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 170
    simpa using h
  have hprev := st286_p170
  have hstep := st286_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p172 : ((141871844261/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT286 (i+1))
      = (∑ i ∈ Finset.range 171, stT286 (i+1)) + stT286 172 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 171
    simpa using h
  have hprev := st286_p171
  have hstep := st286_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p173 : ((1740028855349/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT286 (i+1))
      = (∑ i ∈ Finset.range 172, stT286 (i+1)) + stT286 173 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 172
    simpa using h
  have hprev := st286_p172
  have hstep := st286_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p174 : ((4354781632673/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT286 (i+1))
      = (∑ i ∈ Finset.range 173, stT286 (i+1)) + stT286 174 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 173
    simpa using h
  have hprev := st286_p173
  have hstep := st286_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p175 : ((908585137297/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT286 (i+1))
      = (∑ i ∈ Finset.range 174, stT286 (i+1)) + stT286 175 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 174
    simpa using h
  have hprev := st286_p174
  have hstep := st286_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p176 : ((18057518041683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT286 (i+1))
      = (∑ i ∈ Finset.range 175, stT286 (i+1)) + stT286 176 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 175
    simpa using h
  have hprev := st286_p175
  have hstep := st286_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p177 : ((866050874019/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT286 (i+1))
      = (∑ i ∈ Finset.range 176, stT286 (i+1)) + stT286 177 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 176
    simpa using h
  have hprev := st286_p176
  have hstep := st286_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p178 : ((17500607356573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT286 (i+1))
      = (∑ i ∈ Finset.range 177, stT286 (i+1)) + stT286 178 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 177
    simpa using h
  have hprev := st286_p177
  have hstep := st286_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p179 : ((18220182464383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT286 (i+1))
      = (∑ i ∈ Finset.range 178, stT286 (i+1)) + stT286 179 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 178
    simpa using h
  have hprev := st286_p178
  have hstep := st286_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p180 : ((18002668204327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT286 (i+1))
      = (∑ i ∈ Finset.range 179, stT286 (i+1)) + stT286 180 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 179
    simpa using h
  have hprev := st286_p179
  have hstep := st286_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p181 : ((8647334283701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT286 (i+1))
      = (∑ i ∈ Finset.range 180, stT286 (i+1)) + stT286 181 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 180
    simpa using h
  have hprev := st286_p180
  have hstep := st286_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p182 : ((1095251336593/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT286 (i+1))
      = (∑ i ∈ Finset.range 181, stT286 (i+1)) + stT286 182 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 181
    simpa using h
  have hprev := st286_p181
  have hstep := st286_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p183 : ((18227701379029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT286 (i+1))
      = (∑ i ∈ Finset.range 182, stT286 (i+1)) + stT286 183 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 182
    simpa using h
  have hprev := st286_p182
  have hstep := st286_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p184 : ((18010604829389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT286 (i+1))
      = (∑ i ∈ Finset.range 183, stT286 (i+1)) + stT286 184 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 183
    simpa using h
  have hprev := st286_p183
  have hstep := st286_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p185 : ((8651788618637/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT286 (i+1))
      = (∑ i ∈ Finset.range 184, stT286 (i+1)) + stT286 185 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 184
    simpa using h
  have hprev := st286_p184
  have hstep := st286_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p186 : ((17484295468019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT286 (i+1))
      = (∑ i ∈ Finset.range 185, stT286 (i+1)) + stT286 186 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 185
    simpa using h
  have hprev := st286_p185
  have hstep := st286_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p187 : ((18199142367627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT286 (i+1))
      = (∑ i ∈ Finset.range 186, stT286 (i+1)) + stT286 187 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 186
    simpa using h
  have hprev := st286_p186
  have hstep := st286_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p188 : ((18078269876727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT286 (i+1))
      = (∑ i ∈ Finset.range 187, stT286 (i+1)) + stT286 188 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 187
    simpa using h
  have hprev := st286_p187
  have hstep := st286_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p189 : ((17355431811693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT286 (i+1))
      = (∑ i ∈ Finset.range 188, stT286 (i+1)) + stT286 189 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 188
    simpa using h
  have hprev := st286_p188
  have hstep := st286_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p190 : ((17392550791233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT286 (i+1))
      = (∑ i ∈ Finset.range 189, stT286 (i+1)) + stT286 190 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 189
    simpa using h
  have hprev := st286_p189
  have hstep := st286_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p191 : ((18115933044123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT286 (i+1))
      = (∑ i ∈ Finset.range 190, stT286 (i+1)) + stT286 191 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 190
    simpa using h
  have hprev := st286_p190
  have hstep := st286_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p192 : ((18184686721239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT286 (i+1))
      = (∑ i ∈ Finset.range 191, stT286 (i+1)) + stT286 192 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 191
    simpa using h
  have hprev := st286_p191
  have hstep := st286_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p193 : ((17476505107247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT286 (i+1))
      = (∑ i ∈ Finset.range 192, stT286 (i+1)) + stT286 193 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 192
    simpa using h
  have hprev := st286_p192
  have hstep := st286_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p194 : ((17282617407461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT286 (i+1))
      = (∑ i ∈ Finset.range 193, stT286 (i+1)) + stT286 194 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 193
    simpa using h
  have hprev := st286_p193
  have hstep := st286_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p195 : ((17949235040009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT286 (i+1))
      = (∑ i ∈ Finset.range 194, stT286 (i+1)) + stT286 195 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 194
    simpa using h
  have hprev := st286_p194
  have hstep := st286_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p196 : ((4570001355881/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT286 (i+1))
      = (∑ i ∈ Finset.range 195, stT286 (i+1)) + stT286 196 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 195
    simpa using h
  have hprev := st286_p195
  have hstep := st286_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p197 : ((8845329693459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT286 (i+1))
      = (∑ i ∈ Finset.range 196, stT286 (i+1)) + stT286 197 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 196
    simpa using h
  have hprev := st286_p196
  have hstep := st286_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p198 : ((538193903469/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT286 (i+1))
      = (∑ i ∈ Finset.range 197, stT286 (i+1)) + stT286 198 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 197
    simpa using h
  have hprev := st286_p197
  have hstep := st286_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p199 : ((8845106200247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT286 (i+1))
      = (∑ i ∈ Finset.range 198, stT286 (i+1)) + stT286 199 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 198
    simpa using h
  have hprev := st286_p198
  have hstep := st286_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p200 : ((9140026677833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT286 (i+1))
      = (∑ i ∈ Finset.range 199, stT286 (i+1)) + stT286 200 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 199
    simpa using h
  have hprev := st286_p199
  have hstep := st286_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p201 : ((2247470535881/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT286 (i+1))
      = (∑ i ∈ Finset.range 200, stT286 (i+1)) + stT286 201 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 200
    simpa using h
  have hprev := st286_p200
  have hstep := st286_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p202 : ((4326278428991/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT286 (i+1))
      = (∑ i ∈ Finset.range 201, stT286 (i+1)) + stT286 202 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 201
    simpa using h
  have hprev := st286_p201
  have hstep := st286_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p203 : ((8697929077903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT286 (i+1))
      = (∑ i ∈ Finset.range 202, stT286 (i+1)) + stT286 203 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 202
    simpa using h
  have hprev := st286_p202
  have hstep := st286_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p204 : ((9047741776453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT286 (i+1))
      = (∑ i ∈ Finset.range 203, stT286 (i+1)) + stT286 204 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 203
    simpa using h
  have hprev := st286_p203
  have hstep := st286_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p205 : ((9119784830953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT286 (i+1))
      = (∑ i ∈ Finset.range 204, stT286 (i+1)) + stT286 205 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 204
    simpa using h
  have hprev := st286_p204
  have hstep := st286_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p206 : ((8797140553499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT286 (i+1))
      = (∑ i ∈ Finset.range 205, stT286 (i+1)) + stT286 206 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 205
    simpa using h
  have hprev := st286_p205
  have hstep := st286_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p207 : ((430438036399/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT286 (i+1))
      = (∑ i ∈ Finset.range 206, stT286 (i+1)) + stT286 207 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 206
    simpa using h
  have hprev := st286_p206
  have hstep := st286_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p208 : ((27683628889/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT286 (i+1))
      = (∑ i ∈ Finset.range 207, stT286 (i+1)) + stT286 208 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 207
    simpa using h
  have hprev := st286_p207
  have hstep := st286_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p209 : ((9142905942399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT286 (i+1))
      = (∑ i ∈ Finset.range 208, stT286 (i+1)) + stT286 209 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 208
    simpa using h
  have hprev := st286_p208
  have hstep := st286_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p210 : ((1126030505991/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT286 (i+1))
      = (∑ i ∈ Finset.range 209, stT286 (i+1)) + stT286 210 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 209
    simpa using h
  have hprev := st286_p209
  have hstep := st286_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p211 : ((17340211932993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT286 (i+1))
      = (∑ i ∈ Finset.range 210, stT286 (i+1)) + stT286 211 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 210
    simpa using h
  have hprev := st286_p210
  have hstep := st286_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p212 : ((3463928986071/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT286 (i+1))
      = (∑ i ∈ Finset.range 211, stT286 (i+1)) + stT286 212 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 211
    simpa using h
  have hprev := st286_p211
  have hstep := st286_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p213 : ((17982649283667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT286 (i+1))
      = (∑ i ∈ Finset.range 212, stT286 (i+1)) + stT286 213 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 212
    simpa using h
  have hprev := st286_p212
  have hstep := st286_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p214 : ((571932940141/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT286 (i+1))
      = (∑ i ∈ Finset.range 213, stT286 (i+1)) + stT286 214 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 213
    simpa using h
  have hprev := st286_p213
  have hstep := st286_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p215 : ((17790601306727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT286 (i+1))
      = (∑ i ∈ Finset.range 214, stT286 (i+1)) + stT286 215 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 214
    simpa using h
  have hprev := st286_p214
  have hstep := st286_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p216 : ((17230400130591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT286 (i+1))
      = (∑ i ∈ Finset.range 215, stT286 (i+1)) + stT286 216 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 215
    simpa using h
  have hprev := st286_p215
  have hstep := st286_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p217 : ((17465616182371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT286 (i+1))
      = (∑ i ∈ Finset.range 216, stT286 (i+1)) + stT286 217 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 216
    simpa using h
  have hprev := st286_p216
  have hstep := st286_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p218 : ((18139578422161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT286 (i+1))
      = (∑ i ∈ Finset.range 217, stT286 (i+1)) + stT286 218 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 217
    simpa using h
  have hprev := st286_p217
  have hstep := st286_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p219 : ((18249685711889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT286 (i+1))
      = (∑ i ∈ Finset.range 218, stT286 (i+1)) + stT286 219 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 218
    simpa using h
  have hprev := st286_p218
  have hstep := st286_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p220 : ((17637247825489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT286 (i+1))
      = (∑ i ∈ Finset.range 219, stT286 (i+1)) + stT286 220 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 219
    simpa using h
  have hprev := st286_p219
  have hstep := st286_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p221 : ((17201090688327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT286 (i+1))
      = (∑ i ∈ Finset.range 220, stT286 (i+1)) + stT286 221 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 220
    simpa using h
  have hprev := st286_p220
  have hstep := st286_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p222 : ((17572101698191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT286 (i+1))
      = (∑ i ∈ Finset.range 221, stT286 (i+1)) + stT286 222 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 221
    simpa using h
  have hprev := st286_p221
  have hstep := st286_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p223 : ((18211688815283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT286 (i+1))
      = (∑ i ∈ Finset.range 222, stT286 (i+1)) + stT286 223 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 222
    simpa using h
  have hprev := st286_p222
  have hstep := st286_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p224 : ((18205415517377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT286 (i+1))
      = (∑ i ∈ Finset.range 223, stT286 (i+1)) + stT286 224 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 223
    simpa using h
  have hprev := st286_p223
  have hstep := st286_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p225 : ((17566053864363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT286 (i+1))
      = (∑ i ∈ Finset.range 224, stT286 (i+1)) + stT286 225 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 224
    simpa using h
  have hprev := st286_p224
  have hstep := st286_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p226 : ((17195865760189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT286 (i+1))
      = (∑ i ∈ Finset.range 225, stT286 (i+1)) + stT286 226 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 225
    simpa using h
  have hprev := st286_p225
  have hstep := st286_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p227 : ((17609334657931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT286 (i+1))
      = (∑ i ∈ Finset.range 226, stT286 (i+1)) + stT286 227 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 226
    simpa using h
  have hprev := st286_p226
  have hstep := st286_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p228 : ((3645863524579/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT286 (i+1))
      = (∑ i ∈ Finset.range 227, stT286 (i+1)) + stT286 228 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 227
    simpa using h
  have hprev := st286_p227
  have hstep := st286_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p229 : ((728117244809/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT286 (i+1))
      = (∑ i ∈ Finset.range 228, stT286 (i+1)) + stT286 229 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 228
    simpa using h
  have hprev := st286_p228
  have hstep := st286_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p230 : ((8785019716569/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT286 (i+1))
      = (∑ i ∈ Finset.range 229, stT286 (i+1)) + stT286 230 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 229
    simpa using h
  have hprev := st286_p229
  have hstep := st286_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p231 : ((8595239712713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT286 (i+1))
      = (∑ i ∈ Finset.range 230, stT286 (i+1)) + stT286 231 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 230
    simpa using h
  have hprev := st286_p230
  have hstep := st286_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p232 : ((1757221470457/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT286 (i+1))
      = (∑ i ∈ Finset.range 231, stT286 (i+1)) + stT286 232 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 231
    simpa using h
  have hprev := st286_p231
  have hstep := st286_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p233 : ((9100883821091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT286 (i+1))
      = (∑ i ∈ Finset.range 232, stT286 (i+1)) + stT286 233 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 232
    simpa using h
  have hprev := st286_p232
  have hstep := st286_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p234 : ((9122409186391/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT286 (i+1))
      = (∑ i ∈ Finset.range 233, stT286 (i+1)) + stT286 234 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 233
    simpa using h
  have hprev := st286_p233
  have hstep := st286_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p235 : ((17648371136567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT286 (i+1))
      = (∑ i ∈ Finset.range 234, stT286 (i+1)) + stT286 235 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 234
    simpa using h
  have hprev := st286_p234
  have hstep := st286_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p236 : ((8596755474931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT286 (i+1))
      = (∑ i ∈ Finset.range 235, stT286 (i+1)) + stT286 236 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 235
    simpa using h
  have hprev := st286_p235
  have hstep := st286_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p237 : ((4366906942181/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT286 (i+1))
      = (∑ i ∈ Finset.range 236, stT286 (i+1)) + stT286 237 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 236
    simpa using h
  have hprev := st286_p236
  have hstep := st286_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p238 : ((18114216095051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT286 (i+1))
      = (∑ i ∈ Finset.range 237, stT286 (i+1)) + stT286 238 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 237
    simpa using h
  have hprev := st286_p237
  have hstep := st286_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p239 : ((18306828075317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT286 (i+1))
      = (∑ i ∈ Finset.range 238, stT286 (i+1)) + stT286 239 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 238
    simpa using h
  have hprev := st286_p238
  have hstep := st286_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p240 : ((17804474420801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT286 (i+1))
      = (∑ i ∈ Finset.range 239, stT286 (i+1)) + stT286 240 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 239
    simpa using h
  have hprev := st286_p239
  have hstep := st286_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p241 : ((3448451095903/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT286 (i+1))
      = (∑ i ∈ Finset.range 240, stT286 (i+1)) + stT286 241 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 240
    simpa using h
  have hprev := st286_p240
  have hstep := st286_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p242 : ((17321421183587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT286 (i+1))
      = (∑ i ∈ Finset.range 241, stT286 (i+1)) + stT286 242 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 241
    simpa using h
  have hprev := st286_p241
  have hstep := st286_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p243 : ((17939982426587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT286 (i+1))
      = (∑ i ∈ Finset.range 242, stT286 (i+1)) + stT286 243 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 242
    simpa using h
  have hprev := st286_p242
  have hstep := st286_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p244 : ((18334497737139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT286 (i+1))
      = (∑ i ∈ Finset.range 243, stT286 (i+1)) + stT286 244 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 243
    simpa using h
  have hprev := st286_p243
  have hstep := st286_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p245 : ((9012495928929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT286 (i+1))
      = (∑ i ∈ Finset.range 244, stT286 (i+1)) + stT286 245 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 244
    simpa using h
  have hprev := st286_p244
  have hstep := st286_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p246 : ((1739052368331/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT286 (i+1))
      = (∑ i ∈ Finset.range 245, stT286 (i+1)) + stT286 246 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 245
    simpa using h
  have hprev := st286_p245
  have hstep := st286_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p247 : ((429897579759/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT286 (i+1))
      = (∑ i ∈ Finset.range 246, stT286 (i+1)) + stT286 247 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 246
    simpa using h
  have hprev := st286_p246
  have hstep := st286_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p248 : ((110441999971/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT286 (i+1))
      = (∑ i ∈ Finset.range 247, stT286 (i+1)) + stT286 248 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 247
    simpa using h
  have hprev := st286_p247
  have hstep := st286_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p249 : ((2281003577179/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT286 (i+1))
      = (∑ i ∈ Finset.range 248, stT286 (i+1)) + stT286 249 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 248
    simpa using h
  have hprev := st286_p248
  have hstep := st286_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p250 : ((2280962151311/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT286 (i+1))
      = (∑ i ∈ Finset.range 249, stT286 (i+1)) + stT286 250 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 249
    simpa using h
  have hprev := st286_p249
  have hstep := st286_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p251 : ((17673547721003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT286 (i+1))
      = (∑ i ∈ Finset.range 250, stT286 (i+1)) + stT286 251 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 250
    simpa using h
  have hprev := st286_p250
  have hstep := st286_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p252 : ((17195147847727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT286 (i+1))
      = (∑ i ∈ Finset.range 251, stT286 (i+1)) + stT286 252 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 251
    simpa using h
  have hprev := st286_p251
  have hstep := st286_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p253 : ((17363009145727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT286 (i+1))
      = (∑ i ∈ Finset.range 252, stT286 (i+1)) + stT286 253 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 252
    simpa using h
  have hprev := st286_p252
  have hstep := st286_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p254 : ((17981121340777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT286 (i+1))
      = (∑ i ∈ Finset.range 253, stT286 (i+1)) + stT286 254 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 253
    simpa using h
  have hprev := st286_p253
  have hstep := st286_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p255 : ((18344517875529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT286 (i+1))
      = (∑ i ∈ Finset.range 254, stT286 (i+1)) + stT286 255 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 254
    simpa using h
  have hprev := st286_p254
  have hstep := st286_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p256 : ((3608945479173/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT286 (i+1))
      = (∑ i ∈ Finset.range 255, stT286 (i+1)) + stT286 256 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 255
    simpa using h
  have hprev := st286_p255
  have hstep := st286_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p257 : ((17421495820037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT286 (i+1))
      = (∑ i ∈ Finset.range 256, stT286 (i+1)) + stT286 257 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 256
    simpa using h
  have hprev := st286_p256
  have hstep := st286_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p258 : ((17169988779497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT286 (i+1))
      = (∑ i ∈ Finset.range 257, stT286 (i+1)) + stT286 258 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 257
    simpa using h
  have hprev := st286_p257
  have hstep := st286_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p259 : ((17565756093929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT286 (i+1))
      = (∑ i ∈ Finset.range 258, stT286 (i+1)) + stT286 259 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 258
    simpa using h
  have hprev := st286_p258
  have hstep := st286_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p260 : ((18170651752247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT286 (i+1))
      = (∑ i ∈ Finset.range 259, stT286 (i+1)) + stT286 260 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 259
    simpa using h
  have hprev := st286_p259
  have hstep := st286_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p261 : ((18324286056983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT286 (i+1))
      = (∑ i ∈ Finset.range 260, stT286 (i+1)) + stT286 261 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 260
    simpa using h
  have hprev := st286_p260
  have hstep := st286_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p262 : ((4465760901057/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT286 (i+1))
      = (∑ i ∈ Finset.range 261, stT286 (i+1)) + stT286 262 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 261
    simpa using h
  have hprev := st286_p261
  have hstep := st286_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p263 : ((17286205694657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT286 (i+1))
      = (∑ i ∈ Finset.range 262, stT286 (i+1)) + stT286 263 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 262
    simpa using h
  have hprev := st286_p262
  have hstep := st286_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p264 : ((17210075386431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT286 (i+1))
      = (∑ i ∈ Finset.range 263, stT286 (i+1)) + stT286 264 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 263
    simpa using h
  have hprev := st286_p263
  have hstep := st286_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p265 : ((17712309463941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT286 (i+1))
      = (∑ i ∈ Finset.range 264, stT286 (i+1)) + stT286 265 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 264
    simpa using h
  have hprev := st286_p264
  have hstep := st286_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p266 : ((18260617598637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT286 (i+1))
      = (∑ i ∈ Finset.range 265, stT286 (i+1)) + stT286 266 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 265
    simpa using h
  have hprev := st286_p265
  have hstep := st286_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p267 : ((18281267977207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT286 (i+1))
      = (∑ i ∈ Finset.range 266, stT286 (i+1)) + stT286 267 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 266
    simpa using h
  have hprev := st286_p266
  have hstep := st286_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p268 : ((17755866617143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT286 (i+1))
      = (∑ i ∈ Finset.range 267, stT286 (i+1)) + stT286 268 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 267
    simpa using h
  have hprev := st286_p267
  have hstep := st286_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p269 : ((17229645783217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT286 (i+1))
      = (∑ i ∈ Finset.range 268, stT286 (i+1)) + stT286 269 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 268
    simpa using h
  have hprev := st286_p268
  have hstep := st286_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p270 : ((17241829554817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT286 (i+1))
      = (∑ i ∈ Finset.range 269, stT286 (i+1)) + stT286 270 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 269
    simpa using h
  have hprev := st286_p269
  have hstep := st286_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p271 : ((17776783251393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT286 (i+1))
      = (∑ i ∈ Finset.range 270, stT286 (i+1)) + stT286 271 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 270
    simpa using h
  have hprev := st286_p270
  have hstep := st286_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p272 : ((4572608863209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT286 (i+1))
      = (∑ i ∈ Finset.range 271, stT286 (i+1)) + stT286 272 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 271
    simpa using h
  have hprev := st286_p271
  have hstep := st286_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p273 : ((182669150823/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT286 (i+1))
      = (∑ i ∈ Finset.range 272, stT286 (i+1)) + stT286 273 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 272
    simpa using h
  have hprev := st286_p272
  have hstep := st286_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p274 : ((17732767045267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT286 (i+1))
      = (∑ i ∈ Finset.range 273, stT286 (i+1)) + stT286 274 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 273
    simpa using h
  have hprev := st286_p273
  have hstep := st286_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p275 : ((4305095052809/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT286 (i+1))
      = (∑ i ∈ Finset.range 274, stT286 (i+1)) + stT286 275 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 274
    simpa using h
  have hprev := st286_p274
  have hstep := st286_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p276 : ((4308526048109/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT286 (i+1))
      = (∑ i ∈ Finset.range 275, stT286 (i+1)) + stT286 276 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 275
    simpa using h
  have hprev := st286_p275
  have hstep := st286_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p277 : ((8878694918919/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT286 (i+1))
      = (∑ i ∈ Finset.range 276, stT286 (i+1)) + stT286 277 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 276
    simpa using h
  have hprev := st286_p276
  have hstep := st286_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p278 : ((9139335920799/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT286 (i+1))
      = (∑ i ∈ Finset.range 277, stT286 (i+1)) + stT286 278 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 277
    simpa using h
  have hprev := st286_p277
  have hstep := st286_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p279 : ((9147319371939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT286 (i+1))
      = (∑ i ∈ Finset.range 278, stT286 (i+1)) + stT286 279 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 278
    simpa using h
  have hprev := st286_p278
  have hstep := st286_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p280 : ((4448208643977/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT286 (i+1))
      = (∑ i ∈ Finset.range 279, stT286 (i+1)) + stT286 280 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 279
    simpa using h
  have hprev := st286_p279
  have hstep := st286_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p281 : ((539199977619/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT286 (i+1))
      = (∑ i ∈ Finset.range 280, stT286 (i+1)) + stT286 281 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 280
    simpa using h
  have hprev := st286_p280
  have hstep := st286_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p282 : ((537164288217/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT286 (i+1))
      = (∑ i ∈ Finset.range 281, stT286 (i+1)) + stT286 282 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 281
    simpa using h
  have hprev := st286_p281
  have hstep := st286_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p283 : ((8827948201443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT286 (i+1))
      = (∑ i ∈ Finset.range 282, stT286 (i+1)) + stT286 283 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 282
    simpa using h
  have hprev := st286_p282
  have hstep := st286_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p284 : ((9107538734693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT286 (i+1))
      = (∑ i ∈ Finset.range 283, stT286 (i+1)) + stT286 284 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 283
    simpa using h
  have hprev := st286_p283
  have hstep := st286_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p285 : ((1834695664341/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT286 (i+1))
      = (∑ i ∈ Finset.range 284, stT286 (i+1)) + stT286 285 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 284
    simpa using h
  have hprev := st286_p284
  have hstep := st286_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p286 : ((896611963543/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT286 (i+1))
      = (∑ i ∈ Finset.range 285, stT286 (i+1)) + stT286 286 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 285
    simpa using h
  have hprev := st286_p285
  have hstep := st286_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p287 : ((8677105467449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT286 (i+1))
      = (∑ i ∈ Finset.range 286, stT286 (i+1)) + stT286 287 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 286
    simpa using h
  have hprev := st286_p286
  have hstep := st286_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p288 : ((8570143129073/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT286 (i+1))
      = (∑ i ∈ Finset.range 287, stT286 (i+1)) + stT286 288 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 287
    simpa using h
  have hprev := st286_p287
  have hstep := st286_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p289 : ((4370492404179/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT286 (i+1))
      = (∑ i ∈ Finset.range 288, stT286 (i+1)) + stT286 289 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 288
    simpa using h
  have hprev := st286_p288
  have hstep := st286_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p290 : ((4517182015449/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT286 (i+1))
      = (∑ i ∈ Finset.range 289, stT286 (i+1)) + stT286 290 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 289
    simpa using h
  have hprev := st286_p289
  have hstep := st286_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p291 : ((4593675385929/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT286 (i+1))
      = (∑ i ∈ Finset.range 290, stT286 (i+1)) + stT286 291 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 290
    simpa using h
  have hprev := st286_p290
  have hstep := st286_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p292 : ((566552478211/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT286 (i+1))
      = (∑ i ∈ Finset.range 291, stT286 (i+1)) + stT286 292 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 291
    simpa using h
  have hprev := st286_p291
  have hstep := st286_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p293 : ((4388245132779/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT286 (i+1))
      = (∑ i ∈ Finset.range 292, stT286 (i+1)) + stT286 293 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 292
    simpa using h
  have hprev := st286_p292
  have hstep := st286_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p294 : ((2144024728491/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT286 (i+1))
      = (∑ i ∈ Finset.range 293, stT286 (i+1)) + stT286 294 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 293
    simpa using h
  have hprev := st286_p293
  have hstep := st286_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p295 : ((1727558871861/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT286 (i+1))
      = (∑ i ∈ Finset.range 294, stT286 (i+1)) + stT286 295 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 294
    simpa using h
  have hprev := st286_p294
  have hstep := st286_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p296 : ((8906639602587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT286 (i+1))
      = (∑ i ∈ Finset.range 295, stT286 (i+1)) + stT286 296 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 295
    simpa using h
  have hprev := st286_p295
  have hstep := st286_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p297 : ((9150036944299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT286 (i+1))
      = (∑ i ∈ Finset.range 296, stT286 (i+1)) + stT286 297 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 296
    simpa using h
  have hprev := st286_p296
  have hstep := st286_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p298 : ((9159900992251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT286 (i+1))
      = (∑ i ∈ Finset.range 297, stT286 (i+1)) + stT286 298 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 297
    simpa using h
  have hprev := st286_p297
  have hstep := st286_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p299 : ((1116140621227/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT286 (i+1))
      = (∑ i ∈ Finset.range 298, stT286 (i+1)) + stT286 299 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 298
    simpa using h
  have hprev := st286_p298
  have hstep := st286_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p300 : ((17308026931069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT286 (i+1))
      = (∑ i ∈ Finset.range 299, stT286 (i+1)) + stT286 300 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 299
    simpa using h
  have hprev := st286_p299
  have hstep := st286_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p301 : ((3426322879209/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT286 (i+1))
      = (∑ i ∈ Finset.range 300, stT286 (i+1)) + stT286 301 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 300
    simpa using h
  have hprev := st286_p300
  have hstep := st286_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p302 : ((3494824042653/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT286 (i+1))
      = (∑ i ∈ Finset.range 301, stT286 (i+1)) + stT286 302 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 301
    simpa using h
  have hprev := st286_p301
  have hstep := st286_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p303 : ((18048503104081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT286 (i+1))
      = (∑ i ∈ Finset.range 302, stT286 (i+1)) + stT286 303 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 302
    simpa using h
  have hprev := st286_p302
  have hstep := st286_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p304 : ((18379887055813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT286 (i+1))
      = (∑ i ∈ Finset.range 303, stT286 (i+1)) + stT286 304 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 303
    simpa using h
  have hprev := st286_p303
  have hstep := st286_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p305 : ((18198033049007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT286 (i+1))
      = (∑ i ∈ Finset.range 304, stT286 (i+1)) + stT286 305 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 304
    simpa using h
  have hprev := st286_p304
  have hstep := st286_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p306 : ((17653828546529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT286 (i+1))
      = (∑ i ∈ Finset.range 305, stT286 (i+1)) + stT286 306 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 305
    simpa using h
  have hprev := st286_p305
  have hstep := st286_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p307 : ((17189792282593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT286 (i+1))
      = (∑ i ∈ Finset.range 306, stT286 (i+1)) + stT286 307 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 306
    simpa using h
  have hprev := st286_p306
  have hstep := st286_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p308 : ((17178830412479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT286 (i+1))
      = (∑ i ∈ Finset.range 307, stT286 (i+1)) + stT286 308 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 307
    simpa using h
  have hprev := st286_p307
  have hstep := st286_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p309 : ((17627182375759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT286 (i+1))
      = (∑ i ∈ Finset.range 308, stT286 (i+1)) + stT286 309 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 308
    simpa using h
  have hprev := st286_p308
  have hstep := st286_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p310 : ((36351643821/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT286 (i+1))
      = (∑ i ∈ Finset.range 309, stT286 (i+1)) + stT286 310 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 309
    simpa using h
  have hprev := st286_p309
  have hstep := st286_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p311 : ((18390550701413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT286 (i+1))
      = (∑ i ∈ Finset.range 310, stT286 (i+1)) + stT286 311 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 310
    simpa using h
  have hprev := st286_p310
  have hstep := st286_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p312 : ((4526116910879/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT286 (i+1))
      = (∑ i ∈ Finset.range 311, stT286 (i+1)) + stT286 312 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 311
    simpa using h
  have hprev := st286_p311
  have hstep := st286_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p313 : ((2192956862983/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT286 (i+1))
      = (∑ i ∈ Finset.range 312, stT286 (i+1)) + stT286 313 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 312
    simpa using h
  have hprev := st286_p312
  have hstep := st286_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p314 : ((8572462711357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT286 (i+1))
      = (∑ i ∈ Finset.range 313, stT286 (i+1)) + stT286 314 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 313
    simpa using h
  have hprev := st286_p313
  have hstep := st286_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p315 : ((8607536602357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT286 (i+1))
      = (∑ i ∈ Finset.range 314, stT286 (i+1)) + stT286 315 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 314
    simpa using h
  have hprev := st286_p314
  have hstep := st286_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p316 : ((4424424492719/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT286 (i+1))
      = (∑ i ∈ Finset.range 315, stT286 (i+1)) + stT286 316 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 315
    simpa using h
  have hprev := st286_p315
  have hstep := st286_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p317 : ((18222447182481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT286 (i+1))
      = (∑ i ∈ Finset.range 316, stT286 (i+1)) + stT286 317 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 316
    simpa using h
  have hprev := st286_p316
  have hstep := st286_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p318 : ((18391193571177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT286 (i+1))
      = (∑ i ∈ Finset.range 317, stT286 (i+1)) + stT286 318 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 317
    simpa using h
  have hprev := st286_p317
  have hstep := st286_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p319 : ((9039300695013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT286 (i+1))
      = (∑ i ∈ Finset.range 318, stT286 (i+1)) + stT286 319 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 318
    simpa using h
  have hprev := st286_p318
  have hstep := st286_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p320 : ((8760736933743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT286 (i+1))
      = (∑ i ∈ Finset.range 319, stT286 (i+1)) + stT286 320 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 319
    simpa using h
  have hprev := st286_p319
  have hstep := st286_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p321 : ((1071008988921/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT286 (i+1))
      = (∑ i ∈ Finset.range 320, stT286 (i+1)) + stT286 321 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 320
    simpa using h
  have hprev := st286_p320
  have hstep := st286_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p322 : ((860353095323/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT286 (i+1))
      = (∑ i ∈ Finset.range 321, stT286 (i+1)) + stT286 322 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 321
    simpa using h
  have hprev := st286_p321
  have hstep := st286_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p323 : ((276242686749/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT286 (i+1))
      = (∑ i ∈ Finset.range 322, stT286 (i+1)) + stT286 323 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 322
    simpa using h
  have hprev := st286_p322
  have hstep := st286_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p324 : ((9102722935233/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT286 (i+1))
      = (∑ i ∈ Finset.range 323, stT286 (i+1)) + stT286 324 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 323
    simpa using h
  have hprev := st286_p323
  have hstep := st286_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p325 : ((9200823571683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT286 (i+1))
      = (∑ i ∈ Finset.range 324, stT286 (i+1)) + stT286 325 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 324
    simpa using h
  have hprev := st286_p324
  have hstep := st286_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p326 : ((362556661187/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT286 (i+1))
      = (∑ i ∈ Finset.range 325, stT286 (i+1)) + stT286 326 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 325
    simpa using h
  have hprev := st286_p325
  have hstep := st286_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p327 : ((2197937005961/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT286 (i+1))
      = (∑ i ∈ Finset.range 326, stT286 (i+1)) + stT286 327 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 326
    simpa using h
  have hprev := st286_p326
  have hstep := st286_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p328 : ((2144940328963/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT286 (i+1))
      = (∑ i ∈ Finset.range 327, stT286 (i+1)) + stT286 328 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 327
    simpa using h
  have hprev := st286_p327
  have hstep := st286_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p329 : ((8578436223039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT286 (i+1))
      = (∑ i ∈ Finset.range 328, stT286 (i+1)) + stT286 329 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 328
    simpa using h
  have hprev := st286_p328
  have hstep := st286_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p330 : ((17575169195953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT286 (i+1))
      = (∑ i ∈ Finset.range 329, stT286 (i+1)) + stT286 330 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 329
    simpa using h
  have hprev := st286_p329
  have hstep := st286_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p331 : ((1132370727727/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT286 (i+1))
      = (∑ i ∈ Finset.range 330, stT286 (i+1)) + stT286 331 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 330
    simpa using h
  have hprev := st286_p330
  have hstep := st286_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p332 : ((18404841541907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT286 (i+1))
      = (∑ i ∈ Finset.range 331, stT286 (i+1)) + stT286 332 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 331
    simpa using h
  have hprev := st286_p331
  have hstep := st286_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p333 : ((1139853423823/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT286 (i+1))
      = (∑ i ∈ Finset.range 332, stT286 (i+1)) + stT286 333 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 332
    simpa using h
  have hprev := st286_p332
  have hstep := st286_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p334 : ((277098812407/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT286 (i+1))
      = (∑ i ∈ Finset.range 333, stT286 (i+1)) + stT286 334 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 333
    simpa using h
  have hprev := st286_p333
  have hstep := st286_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p335 : ((4310678087821/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT286 (i+1))
      = (∑ i ∈ Finset.range 334, stT286 (i+1)) + stT286 335 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 334
    simpa using h
  have hprev := st286_p334
  have hstep := st286_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p336 : ((16698165981/9765625000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT286 (i+1))
      = (∑ i ∈ Finset.range 335, stT286 (i+1)) + stT286 336 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 335
    simpa using h
  have hprev := st286_p335
  have hstep := st286_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p337 : ((869945185497/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT286 (i+1))
      = (∑ i ∈ Finset.range 336, stT286 (i+1)) + stT286 337 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 336
    simpa using h
  have hprev := st286_p336
  have hstep := st286_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p338 : ((4484362113631/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT286 (i+1))
      = (∑ i ∈ Finset.range 337, stT286 (i+1)) + stT286 338 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 337
    simpa using h
  have hprev := st286_p337
  have hstep := st286_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p339 : ((18351101687649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT286 (i+1))
      = (∑ i ∈ Finset.range 338, stT286 (i+1)) + stT286 339 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 338
    simpa using h
  have hprev := st286_p338
  have hstep := st286_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p340 : ((18363815978393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT286 (i+1))
      = (∑ i ∈ Finset.range 339, stT286 (i+1)) + stT286 340 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 339
    simpa using h
  have hprev := st286_p339
  have hstep := st286_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p341 : ((2246145486249/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT286 (i+1))
      = (∑ i ∈ Finset.range 340, stT286 (i+1)) + stT286 341 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 340
    simpa using h
  have hprev := st286_p340
  have hstep := st286_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p342 : ((17430235824903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT286 (i+1))
      = (∑ i ∈ Finset.range 341, stT286 (i+1)) + stT286 342 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 341
    simpa using h
  have hprev := st286_p341
  have hstep := st286_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p343 : ((17102258316003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT286 (i+1))
      = (∑ i ∈ Finset.range 342, stT286 (i+1)) + stT286 343 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 342
    simpa using h
  have hprev := st286_p342
  have hstep := st286_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p344 : ((17198686540227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT286 (i+1))
      = (∑ i ∈ Finset.range 343, stT286 (i+1)) + stT286 344 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 343
    simpa using h
  have hprev := st286_p343
  have hstep := st286_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p345 : ((8827292439561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT286 (i+1))
      = (∑ i ∈ Finset.range 344, stT286 (i+1)) + stT286 345 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 344
    simpa using h
  have hprev := st286_p344
  have hstep := st286_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p346 : ((18173072329251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT286 (i+1))
      = (∑ i ∈ Finset.range 345, stT286 (i+1)) + stT286 346 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 345
    simpa using h
  have hprev := st286_p345
  have hstep := st286_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p347 : ((3684021752927/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT286 (i+1))
      = (∑ i ∈ Finset.range 346, stT286 (i+1)) + stT286 347 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 346
    simpa using h
  have hprev := st286_p346
  have hstep := st286_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p348 : ((2279863378137/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT286 (i+1))
      = (∑ i ∈ Finset.range 347, stT286 (i+1)) + stT286 348 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 347
    simpa using h
  have hprev := st286_p347
  have hstep := st286_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p349 : ((17746954871/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT286 (i+1))
      = (∑ i ∈ Finset.range 348, stT286 (i+1)) + stT286 349 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 348
    simpa using h
  have hprev := st286_p348
  have hstep := st286_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p350 : ((8628649331287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT286 (i+1))
      = (∑ i ∈ Finset.range 349, stT286 (i+1)) + stT286 350 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 349
    simpa using h
  have hprev := st286_p349
  have hstep := st286_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p351 : ((3415656218909/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT286 (i+1))
      = (∑ i ∈ Finset.range 350, stT286 (i+1)) + stT286 351 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 350
    simpa using h
  have hprev := st286_p350
  have hstep := st286_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p352 : ((8457245039/4882812500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT286 (i+1))
      = (∑ i ∈ Finset.range 351, stT286 (i+1)) + stT286 352 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 351
    simpa using h
  have hprev := st286_p351
  have hstep := st286_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p353 : ((8915376321721/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT286 (i+1))
      = (∑ i ∈ Finset.range 352, stT286 (i+1)) + stT286 353 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 352
    simpa using h
  have hprev := st286_p352
  have hstep := st286_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p354 : ((914579146083/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT286 (i+1))
      = (∑ i ∈ Finset.range 353, stT286 (i+1)) + stT286 354 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 353
    simpa using h
  have hprev := st286_p353
  have hstep := st286_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p355 : ((920953912267/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT286 (i+1))
      = (∑ i ∈ Finset.range 354, stT286 (i+1)) + stT286 355 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 354
    simpa using h
  have hprev := st286_p354
  have hstep := st286_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p356 : ((18136679408169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT286 (i+1))
      = (∑ i ∈ Finset.range 355, stT286 (i+1)) + stT286 356 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 355
    simpa using h
  have hprev := st286_p355
  have hstep := st286_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p357 : ((17618640539541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT286 (i+1))
      = (∑ i ∈ Finset.range 356, stT286 (i+1)) + stT286 357 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 356
    simpa using h
  have hprev := st286_p356
  have hstep := st286_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p358 : ((2147547628777/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT286 (i+1))
      = (∑ i ∈ Finset.range 357, stT286 (i+1)) + stT286 358 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 357
    simpa using h
  have hprev := st286_p357
  have hstep := st286_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p359 : ((533936188173/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT286 (i+1))
      = (∑ i ∈ Finset.range 358, stT286 (i+1)) + stT286 359 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 358
    simpa using h
  have hprev := st286_p358
  have hstep := st286_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p360 : ((4347582562203/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT286 (i+1))
      = (∑ i ∈ Finset.range 359, stT286 (i+1)) + stT286 360 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 359
    simpa using h
  have hprev := st286_p359
  have hstep := st286_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p361 : ((1119358091857/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT286 (i+1))
      = (∑ i ∈ Finset.range 360, stT286 (i+1)) + stT286 361 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 360
    simpa using h
  have hprev := st286_p360
  have hstep := st286_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p362 : ((91672616783/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT286 (i+1))
      = (∑ i ∈ Finset.range 361, stT286 (i+1)) + stT286 362 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 361
    simpa using h
  have hprev := st286_p361
  have hstep := st286_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p363 : ((9207060465001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT286 (i+1))
      = (∑ i ∈ Finset.range 362, stT286 (i+1)) + stT286 363 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 362
    simpa using h
  have hprev := st286_p362
  have hstep := st286_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p364 : ((3620678751891/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT286 (i+1))
      = (∑ i ∈ Finset.range 363, stT286 (i+1)) + stT286 364 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 363
    simpa using h
  have hprev := st286_p363
  have hstep := st286_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p365 : ((17585929465119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT286 (i+1))
      = (∑ i ∈ Finset.range 364, stT286 (i+1)) + stT286 365 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 364
    simpa using h
  have hprev := st286_p364
  have hstep := st286_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p366 : ((8581877850317/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT286 (i+1))
      = (∑ i ∈ Finset.range 365, stT286 (i+1)) + stT286 366 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 365
    simpa using h
  have hprev := st286_p365
  have hstep := st286_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p367 : ((1708071448897/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT286 (i+1))
      = (∑ i ∈ Finset.range 366, stT286 (i+1)) + stT286 367 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 366
    simpa using h
  have hprev := st286_p366
  have hstep := st286_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p368 : ((8691471279167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT286 (i+1))
      = (∑ i ∈ Finset.range 367, stT286 (i+1)) + stT286 368 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 367
    simpa using h
  have hprev := st286_p367
  have hstep := st286_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p369 : ((894770911281/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT286 (i+1))
      = (∑ i ∈ Finset.range 368, stT286 (i+1)) + stT286 369 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 368
    simpa using h
  have hprev := st286_p368
  have hstep := st286_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p370 : ((3665009104999/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT286 (i+1))
      = (∑ i ∈ Finset.range 369, stT286 (i+1)) + stT286 370 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 369
    simpa using h
  have hprev := st286_p369
  have hstep := st286_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p371 : ((18428624372213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT286 (i+1))
      = (∑ i ∈ Finset.range 370, stT286 (i+1)) + stT286 371 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 370
    simpa using h
  have hprev := st286_p370
  have hstep := st286_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p372 : ((18149267429509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT286 (i+1))
      = (∑ i ∈ Finset.range 371, stT286 (i+1)) + stT286 372 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 371
    simpa using h
  have hprev := st286_p371
  have hstep := st286_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p373 : ((8822779081873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT286 (i+1))
      = (∑ i ∈ Finset.range 372, stT286 (i+1)) + stT286 373 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 372
    simpa using h
  have hprev := st286_p372
  have hstep := st286_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p374 : ((8599889592193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT286 (i+1))
      = (∑ i ∈ Finset.range 373, stT286 (i+1)) + stT286 374 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 373
    simpa using h
  have hprev := st286_p373
  have hstep := st286_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p375 : ((8529630029507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT286 (i+1))
      = (∑ i ∈ Finset.range 374, stT286 (i+1)) + stT286 375 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 374
    simpa using h
  have hprev := st286_p374
  have hstep := st286_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p376 : ((2162520781233/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT286 (i+1))
      = (∑ i ∈ Finset.range 375, stT286 (i+1)) + stT286 376 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 375
    simpa using h
  have hprev := st286_p375
  have hstep := st286_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p377 : ((8894088280517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT286 (i+1))
      = (∑ i ∈ Finset.range 376, stT286 (i+1)) + stT286 377 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 376
    simpa using h
  have hprev := st286_p376
  have hstep := st286_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p378 : ((9127544135849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT286 (i+1))
      = (∑ i ∈ Finset.range 377, stT286 (i+1)) + stT286 378 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 377
    simpa using h
  have hprev := st286_p377
  have hstep := st286_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p379 : ((18446786508703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT286 (i+1))
      = (∑ i ∈ Finset.range 378, stT286 (i+1)) + stT286 379 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 378
    simpa using h
  have hprev := st286_p378
  have hstep := st286_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p380 : ((18260728626633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT286 (i+1))
      = (∑ i ∈ Finset.range 379, stT286 (i+1)) + stT286 380 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 379
    simpa using h
  have hprev := st286_p379
  have hstep := st286_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p381 : ((17798943890661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT286 (i+1))
      = (∑ i ∈ Finset.range 380, stT286 (i+1)) + stT286 381 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 380
    simpa using h
  have hprev := st286_p380
  have hstep := st286_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p382 : ((17310339288301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT286 (i+1))
      = (∑ i ∈ Finset.range 381, stT286 (i+1)) + stT286 382 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 381
    simpa using h
  have hprev := st286_p381
  have hstep := st286_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p383 : ((1705571791627/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT286 (i+1))
      = (∑ i ∈ Finset.range 382, stT286 (i+1)) + stT286 383 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 382
    simpa using h
  have hprev := st286_p382
  have hstep := st286_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p384 : ((1716914656121/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT286 (i+1))
      = (∑ i ∈ Finset.range 383, stT286 (i+1)) + stT286 384 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 383
    simpa using h
  have hprev := st286_p383
  have hstep := st286_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p385 : ((17588941266169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT286 (i+1))
      = (∑ i ∈ Finset.range 384, stT286 (i+1)) + stT286 385 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 384
    simpa using h
  have hprev := st286_p384
  have hstep := st286_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p386 : ((18092955490921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT286 (i+1))
      = (∑ i ∈ Finset.range 385, stT286 (i+1)) + stT286 386 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 385
    simpa using h
  have hprev := st286_p385
  have hstep := st286_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p387 : ((18417125914753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT286 (i+1))
      = (∑ i ∈ Finset.range 386, stT286 (i+1)) + stT286 387 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 386
    simpa using h
  have hprev := st286_p386
  have hstep := st286_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p388 : ((18393519073753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT286 (i+1))
      = (∑ i ∈ Finset.range 387, stT286 (i+1)) + stT286 388 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 387
    simpa using h
  have hprev := st286_p387
  have hstep := st286_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p389 : ((18035961780301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT286 (i+1))
      = (∑ i ∈ Finset.range 388, stT286 (i+1)) + stT286 389 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 388
    simpa using h
  have hprev := st286_p388
  have hstep := st286_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p390 : ((17530277405281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT286 (i+1))
      = (∑ i ∈ Finset.range 389, stT286 (i+1)) + stT286 390 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 389
    simpa using h
  have hprev := st286_p389
  have hstep := st286_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p391 : ((17136498487147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT286 (i+1))
      = (∑ i ∈ Finset.range 390, stT286 (i+1)) + stT286 391 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 390
    simpa using h
  have hprev := st286_p390
  have hstep := st286_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p392 : ((17055074013823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT286 (i+1))
      = (∑ i ∈ Finset.range 391, stT286 (i+1)) + stT286 392 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 391
    simpa using h
  have hprev := st286_p391
  have hstep := st286_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p393 : ((17325894002863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT286 (i+1))
      = (∑ i ∈ Finset.range 392, stT286 (i+1)) + stT286 393 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 392
    simpa using h
  have hprev := st286_p392
  have hstep := st286_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p394 : ((17810412936111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT286 (i+1))
      = (∑ i ∈ Finset.range 393, stT286 (i+1)) + stT286 394 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 393
    simpa using h
  have hprev := st286_p393
  have hstep := st286_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p395 : ((18263901611079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT286 (i+1))
      = (∑ i ∈ Finset.range 394, stT286 (i+1)) + stT286 395 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 394
    simpa using h
  have hprev := st286_p394
  have hstep := st286_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p396 : ((18459459505887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT286 (i+1))
      = (∑ i ∈ Finset.range 395, stT286 (i+1)) + stT286 396 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 395
    simpa using h
  have hprev := st286_p395
  have hstep := st286_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p397 : ((18300833416727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT286 (i+1))
      = (∑ i ∈ Finset.range 396, stT286 (i+1)) + stT286 397 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 396
    simpa using h
  have hprev := st286_p396
  have hstep := st286_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p398 : ((17868248346707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT286 (i+1))
      = (∑ i ∈ Finset.range 397, stT286 (i+1)) + stT286 398 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 397
    simpa using h
  have hprev := st286_p397
  have hstep := st286_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p399 : ((8688190408663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT286 (i+1))
      = (∑ i ∈ Finset.range 398, stT286 (i+1)) + stT286 399 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 398
    simpa using h
  have hprev := st286_p398
  have hstep := st286_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p400 : ((17067002698571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT286 (i+1))
      = (∑ i ∈ Finset.range 399, stT286 (i+1)) + stT286 400 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 399
    simpa using h
  have hprev := st286_p399
  have hstep := st286_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p401 : ((17090456391787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT286 (i+1))
      = (∑ i ∈ Finset.range 400, stT286 (i+1)) + stT286 401 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 400
    simpa using h
  have hprev := st286_p400
  have hstep := st286_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p402 : ((17433790166569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT286 (i+1))
      = (∑ i ∈ Finset.range 401, stT286 (i+1)) + stT286 402 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 401
    simpa using h
  have hprev := st286_p401
  have hstep := st286_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p403 : ((4482336331351/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT286 (i+1))
      = (∑ i ∈ Finset.range 402, stT286 (i+1)) + stT286 403 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 402
    simpa using h
  have hprev := st286_p402
  have hstep := st286_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p404 : ((9168832905387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT286 (i+1))
      = (∑ i ∈ Finset.range 403, stT286 (i+1)) + stT286 404 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 403
    simpa using h
  have hprev := st286_p403
  have hstep := st286_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p405 : ((9231668277349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT286 (i+1))
      = (∑ i ∈ Finset.range 404, stT286 (i+1)) + stT286 405 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 404
    simpa using h
  have hprev := st286_p404
  have hstep := st286_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p406 : ((9123816581369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT286 (i+1))
      = (∑ i ∈ Finset.range 405, stT286 (i+1)) + stT286 406 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 405
    simpa using h
  have hprev := st286_p405
  have hstep := st286_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p407 : ((8897261157813/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT286 (i+1))
      = (∑ i ∈ Finset.range 406, stT286 (i+1)) + stT286 407 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 406
    simpa using h
  have hprev := st286_p406
  have hstep := st286_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p408 : ((8659623657517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT286 (i+1))
      = (∑ i ∈ Finset.range 407, stT286 (i+1)) + stT286 408 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 407
    simpa using h
  have hprev := st286_p407
  have hstep := st286_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p409 : ((21306895249/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT286 (i+1))
      = (∑ i ∈ Finset.range 408, stT286 (i+1)) + stT286 409 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 408
    simpa using h
  have hprev := st286_p408
  have hstep := st286_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p410 : ((427514983011/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT286 (i+1))
      = (∑ i ∈ Finset.range 409, stT286 (i+1)) + stT286 410 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 409
    simpa using h
  have hprev := st286_p409
  have hstep := st286_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p411 : ((2182166876781/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT286 (i+1))
      = (∑ i ∈ Finset.range 410, stT286 (i+1)) + stT286 411 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 410
    simpa using h
  have hprev := st286_p410
  have hstep := st286_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p412 : ((44872094513/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT286 (i+1))
      = (∑ i ∈ Finset.range 411, stT286 (i+1)) + stT286 412 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 411
    simpa using h
  have hprev := st286_p411
  have hstep := st286_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p413 : ((4586878114217/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT286 (i+1))
      = (∑ i ∈ Finset.range 412, stT286 (i+1)) + stT286 413 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 412
    simpa using h
  have hprev := st286_p412
  have hstep := st286_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p414 : ((18470487356509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT286 (i+1))
      = (∑ i ∈ Finset.range 413, stT286 (i+1)) + stT286 414 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 413
    simpa using h
  have hprev := st286_p413
  have hstep := st286_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p415 : ((1826268810247/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT286 (i+1))
      = (∑ i ∈ Finset.range 414, stT286 (i+1)) + stT286 415 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 414
    simpa using h
  have hprev := st286_p414
  have hstep := st286_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p416 : ((4455049873597/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT286 (i+1))
      = (∑ i ∈ Finset.range 415, stT286 (i+1)) + stT286 416 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 415
    simpa using h
  have hprev := st286_p415
  have hstep := st286_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p417 : ((4336155861633/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT286 (i+1))
      = (∑ i ∈ Finset.range 416, stT286 (i+1)) + stT286 417 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 416
    simpa using h
  have hprev := st286_p416
  have hstep := st286_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p418 : ((2131335964873/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT286 (i+1))
      = (∑ i ∈ Finset.range 417, stT286 (i+1)) + stT286 418 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 417
    simpa using h
  have hprev := st286_p417
  have hstep := st286_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p419 : ((2133700454913/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT286 (i+1))
      = (∑ i ∈ Finset.range 418, stT286 (i+1)) + stT286 419 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 418
    simpa using h
  have hprev := st286_p418
  have hstep := st286_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p420 : ((8695760178327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT286 (i+1))
      = (∑ i ∈ Finset.range 419, stT286 (i+1)) + stT286 420 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 419
    simpa using h
  have hprev := st286_p419
  have hstep := st286_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p421 : ((8935905410017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT286 (i+1))
      = (∑ i ∈ Finset.range 420, stT286 (i+1)) + stT286 421 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 420
    simpa using h
  have hprev := st286_p420
  have hstep := st286_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p422 : ((9148485042457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT286 (i+1))
      = (∑ i ∈ Finset.range 421, stT286 (i+1)) + stT286 422 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 421
    simpa using h
  have hprev := st286_p421
  have hstep := st286_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p423 : ((9239856698041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT286 (i+1))
      = (∑ i ∈ Finset.range 422, stT286 (i+1)) + stT286 423 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 422
    simpa using h
  have hprev := st286_p422
  have hstep := st286_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p424 : ((9170417519329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT286 (i+1))
      = (∑ i ∈ Finset.range 423, stT286 (i+1)) + stT286 424 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 423
    simpa using h
  have hprev := st286_p423
  have hstep := st286_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p425 : ((8971204512329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT286 (i+1))
      = (∑ i ∈ Finset.range 424, stT286 (i+1)) + stT286 425 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 424
    simpa using h
  have hprev := st286_p424
  have hstep := st286_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p426 : ((8729440921341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT286 (i+1))
      = (∑ i ∈ Finset.range 425, stT286 (i+1)) + stT286 426 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 425
    simpa using h
  have hprev := st286_p425
  have hstep := st286_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p427 : ((4275006719031/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT286 (i+1))
      = (∑ i ∈ Finset.range 426, stT286 (i+1)) + stT286 427 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 426
    simpa using h
  have hprev := st286_p426
  have hstep := st286_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p428 : ((8509999668873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT286 (i+1))
      = (∑ i ∈ Finset.range 427, stT286 (i+1)) + stT286 428 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 427
    simpa using h
  have hprev := st286_p427
  have hstep := st286_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p429 : ((8625972569301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT286 (i+1))
      = (∑ i ∈ Finset.range 428, stT286 (i+1)) + stT286 429 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 428
    simpa using h
  have hprev := st286_p428
  have hstep := st286_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p430 : ((884769032131/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT286 (i+1))
      = (∑ i ∈ Finset.range 429, stT286 (i+1)) + stT286 430 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 429
    simpa using h
  have hprev := st286_p429
  have hstep := st286_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p431 : ((18160744704263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT286 (i+1))
      = (∑ i ∈ Finset.range 430, stT286 (i+1)) + stT286 431 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 430
    simpa using h
  have hprev := st286_p430
  have hstep := st286_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p432 : ((4612711078847/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT286 (i+1))
      = (∑ i ∈ Finset.range 431, stT286 (i+1)) + stT286 432 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 431
    simpa using h
  have hprev := st286_p431
  have hstep := st286_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p433 : ((4611022355867/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT286 (i+1))
      = (∑ i ∈ Finset.range 432, stT286 (i+1)) + stT286 433 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 432
    simpa using h
  have hprev := st286_p432
  have hstep := st286_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p434 : ((907228379987/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT286 (i+1))
      = (∑ i ∈ Finset.range 433, stT286 (i+1)) + stT286 434 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 433
    simpa using h
  have hprev := st286_p433
  have hstep := st286_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p435 : ((4419667268673/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT286 (i+1))
      = (∑ i ∈ Finset.range 434, stT286 (i+1)) + stT286 435 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 434
    simpa using h
  have hprev := st286_p434
  have hstep := st286_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p436 : ((8620455274641/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT286 (i+1))
      = (∑ i ∈ Finset.range 435, stT286 (i+1)) + stT286 436 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 435
    simpa using h
  have hprev := st286_p435
  have hstep := st286_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p437 : ((17012466865167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT286 (i+1))
      = (∑ i ∈ Finset.range 436, stT286 (i+1)) + stT286 437 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 436
    simpa using h
  have hprev := st286_p436
  have hstep := st286_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p438 : ((17086650498757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT286 (i+1))
      = (∑ i ∈ Finset.range 437, stT286 (i+1)) + stT286 438 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 437
    simpa using h
  have hprev := st286_p437
  have hstep := st286_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p439 : ((17431695968653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT286 (i+1))
      = (∑ i ∈ Finset.range 438, stT286 (i+1)) + stT286 439 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 438
    simpa using h
  have hprev := st286_p438
  have hstep := st286_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p440 : ((8952700101767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT286 (i+1))
      = (∑ i ∈ Finset.range 439, stT286 (i+1)) + stT286 440 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 439
    simpa using h
  have hprev := st286_p439
  have hstep := st286_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p441 : ((9157210373447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT286 (i+1))
      = (∑ i ∈ Finset.range 440, stT286 (i+1)) + stT286 441 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 440
    simpa using h
  have hprev := st286_p440
  have hstep := st286_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p442 : ((18493276462867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT286 (i+1))
      = (∑ i ∈ Finset.range 441, stT286 (i+1)) + stT286 442 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 441
    simpa using h
  have hprev := st286_p441
  have hstep := st286_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p443 : ((9185377140891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT286 (i+1))
      = (∑ i ∈ Finset.range 442, stT286 (i+1)) + stT286 443 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 442
    simpa using h
  have hprev := st286_p442
  have hstep := st286_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p444 : ((3599462277747/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT286 (i+1))
      = (∑ i ∈ Finset.range 443, stT286 (i+1)) + stT286 444 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 443
    simpa using h
  have hprev := st286_p443
  have hstep := st286_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p445 : ((17523330333037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT286 (i+1))
      = (∑ i ∈ Finset.range 444, stT286 (i+1)) + stT286 445 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 444
    simpa using h
  have hprev := st286_p444
  have hstep := st286_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p446 : ((3427590961691/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT286 (i+1))
      = (∑ i ∈ Finset.range 445, stT286 (i+1)) + stT286 446 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 445
    simpa using h
  have hprev := st286_p445
  have hstep := st286_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p447 : ((16993586848103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT286 (i+1))
      = (∑ i ∈ Finset.range 446, stT286 (i+1)) + stT286 447 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 446
    simpa using h
  have hprev := st286_p446
  have hstep := st286_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p448 : ((17146211546033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT286 (i+1))
      = (∑ i ∈ Finset.range 447, stT286 (i+1)) + stT286 448 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 447
    simpa using h
  have hprev := st286_p447
  have hstep := st286_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p449 : ((8767286859179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT286 (i+1))
      = (∑ i ∈ Finset.range 448, stT286 (i+1)) + stT286 449 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 448
    simpa using h
  have hprev := st286_p448
  have hstep := st286_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p450 : ((9002843195343/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT286 (i+1))
      = (∑ i ∈ Finset.range 449, stT286 (i+1)) + stT286 450 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 449
    simpa using h
  have hprev := st286_p449
  have hstep := st286_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p451 : ((9187793950999/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT286 (i+1))
      = (∑ i ∈ Finset.range 450, stT286 (i+1)) + stT286 451 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 450
    simpa using h
  have hprev := st286_p450
  have hstep := st286_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p452 : ((9250571959479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT286 (i+1))
      = (∑ i ∈ Finset.range 451, stT286 (i+1)) + stT286 452 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 451
    simpa using h
  have hprev := st286_p451
  have hstep := st286_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p453 : ((2291852173239/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT286 (i+1))
      = (∑ i ∈ Finset.range 452, stT286 (i+1)) + stT286 453 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 452
    simpa using h
  have hprev := st286_p452
  have hstep := st286_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p454 : ((560681039559/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT286 (i+1))
      = (∑ i ∈ Finset.range 453, stT286 (i+1)) + stT286 454 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 453
    simpa using h
  have hprev := st286_p453
  have hstep := st286_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p455 : ((2184193069229/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT286 (i+1))
      = (∑ i ∈ Finset.range 454, stT286 (i+1)) + stT286 455 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 454
    simpa using h
  have hprev := st286_p454
  have hstep := st286_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p456 : ((3421799530669/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT286 (i+1))
      = (∑ i ∈ Finset.range 455, stT286 (i+1)) + stT286 456 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 455
    simpa using h
  have hprev := st286_p455
  have hstep := st286_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p457 : ((1698617941289/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT286 (i+1))
      = (∑ i ∈ Finset.range 456, stT286 (i+1)) + stT286 457 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 456
    simpa using h
  have hprev := st286_p456
  have hstep := st286_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p458 : ((3430110593073/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT286 (i+1))
      = (∑ i ∈ Finset.range 457, stT286 (i+1)) + stT286 458 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 457
    simpa using h
  have hprev := st286_p457
  have hstep := st286_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p459 : ((3507804568761/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT286 (i+1))
      = (∑ i ∈ Finset.range 458, stT286 (i+1)) + stT286 459 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 458
    simpa using h
  have hprev := st286_p458
  have hstep := st286_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p460 : ((18004943338633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT286 (i+1))
      = (∑ i ∈ Finset.range 459, stT286 (i+1)) + stT286 460 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 459
    simpa using h
  have hprev := st286_p459
  have hstep := st286_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p461 : ((18373959949131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT286 (i+1))
      = (∑ i ∈ Finset.range 460, stT286 (i+1)) + stT286 461 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 460
    simpa using h
  have hprev := st286_p460
  have hstep := st286_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p462 : ((3701839950077/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT286 (i+1))
      = (∑ i ∈ Finset.range 461, stT286 (i+1)) + stT286 462 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 461
    simpa using h
  have hprev := st286_p461
  have hstep := st286_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p463 : ((3672297822497/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT286 (i+1))
      = (∑ i ∈ Finset.range 462, stT286 (i+1)) + stT286 463 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 462
    simpa using h
  have hprev := st286_p462
  have hstep := st286_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p464 : ((1798643738797/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT286 (i+1))
      = (∑ i ∈ Finset.range 463, stT286 (i+1)) + stT286 464 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 463
    simpa using h
  have hprev := st286_p463
  have hstep := st286_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p465 : ((8761351048941/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT286 (i+1))
      = (∑ i ∈ Finset.range 464, stT286 (i+1)) + stT286 465 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 464
    simpa using h
  have hprev := st286_p464
  have hstep := st286_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p466 : ((4285062028239/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT286 (i+1))
      = (∑ i ∈ Finset.range 465, stT286 (i+1)) + stT286 466 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 465
    simpa using h
  have hprev := st286_p465
  have hstep := st286_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p467 : ((530563902643/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT286 (i+1))
      = (∑ i ∈ Finset.range 466, stT286 (i+1)) + stT286 467 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 466
    simpa using h
  have hprev := st286_p466
  have hstep := st286_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p468 : ((8547015633913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT286 (i+1))
      = (∑ i ∈ Finset.range 467, stT286 (i+1)) + stT286 468 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 467
    simpa using h
  have hprev := st286_p467
  have hstep := st286_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p469 : ((17445185922401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT286 (i+1))
      = (∑ i ∈ Finset.range 468, stT286 (i+1)) + stT286 469 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 468
    simpa using h
  have hprev := st286_p468
  have hstep := st286_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p470 : ((17904216554741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT286 (i+1))
      = (∑ i ∈ Finset.range 469, stT286 (i+1)) + stT286 470 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 469
    simpa using h
  have hprev := st286_p469
  have hstep := st286_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p471 : ((4576553889129/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT286 (i+1))
      = (∑ i ∈ Finset.range 470, stT286 (i+1)) + stT286 471 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 470
    simpa using h
  have hprev := st286_p470
  have hstep := st286_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p472 : ((18507952444311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT286 (i+1))
      = (∑ i ∈ Finset.range 471, stT286 (i+1)) + stT286 472 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 471
    simpa using h
  have hprev := st286_p471
  have hstep := st286_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p473 : ((18438517895301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT286 (i+1))
      = (∑ i ∈ Finset.range 472, stT286 (i+1)) + stT286 473 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 472
    simpa using h
  have hprev := st286_p472
  have hstep := st286_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p474 : ((18123533680613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT286 (i+1))
      = (∑ i ∈ Finset.range 473, stT286 (i+1)) + stT286 474 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 473
    simpa using h
  have hprev := st286_p473
  have hstep := st286_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p475 : ((17674979517413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT286 (i+1))
      = (∑ i ∈ Finset.range 474, stT286 (i+1)) + stT286 475 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 474
    simpa using h
  have hprev := st286_p474
  have hstep := st286_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p476 : ((17250815093813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT286 (i+1))
      = (∑ i ∈ Finset.range 475, stT286 (i+1)) + stT286 476 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 475
    simpa using h
  have hprev := st286_p475
  have hstep := st286_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p477 : ((8499603689401/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT286 (i+1))
      = (∑ i ∈ Finset.range 476, stT286 (i+1)) + stT286 477 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 476
    simpa using h
  have hprev := st286_p476
  have hstep := st286_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p478 : ((17007074012213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT286 (i+1))
      = (∑ i ∈ Finset.range 477, stT286 (i+1)) + stT286 478 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 477
    simpa using h
  have hprev := st286_p477
  have hstep := st286_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p479 : ((2158830104751/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT286 (i+1))
      = (∑ i ∈ Finset.range 478, stT286 (i+1)) + stT286 479 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 478
    simpa using h
  have hprev := st286_p478
  have hstep := st286_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p480 : ((2212234825491/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT286 (i+1))
      = (∑ i ∈ Finset.range 479, stT286 (i+1)) + stT286 480 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 479
    simpa using h
  have hprev := st286_p479
  have hstep := st286_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p481 : ((1133823052713/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT286 (i+1))
      = (∑ i ∈ Finset.range 480, stT286 (i+1)) + stT286 481 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 480
    simpa using h
  have hprev := st286_p480
  have hstep := st286_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p482 : ((9224284410471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT286 (i+1))
      = (∑ i ∈ Finset.range 481, stT286 (i+1)) + stT286 482 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 481
    simpa using h
  have hprev := st286_p481
  have hstep := st286_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p483 : ((18515712199387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT286 (i+1))
      = (∑ i ∈ Finset.range 482, stT286 (i+1)) + stT286 483 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 482
    simpa using h
  have hprev := st286_p482
  have hstep := st286_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p484 : ((18320689692633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT286 (i+1))
      = (∑ i ∈ Finset.range 483, stT286 (i+1)) + stT286 484 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 483
    simpa using h
  have hprev := st286_p483
  have hstep := st286_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p485 : ((896526224223/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT286 (i+1))
      = (∑ i ∈ Finset.range 484, stT286 (i+1)) + stT286 485 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 484
    simpa using h
  have hprev := st286_p484
  have hstep := st286_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p486 : ((1747748013613/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT286 (i+1))
      = (∑ i ∈ Finset.range 485, stT286 (i+1)) + stT286 486 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 485
    simpa using h
  have hprev := st286_p485
  have hstep := st286_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p487 : ((1711391137633/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT286 (i+1))
      = (∑ i ∈ Finset.range 486, stT286 (i+1)) + stT286 487 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 486
    simpa using h
  have hprev := st286_p486
  have hstep := st286_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p488 : ((8480526271163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT286 (i+1))
      = (∑ i ∈ Finset.range 487, stT286 (i+1)) + stT286 488 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 487
    simpa using h
  have hprev := st286_p487
  have hstep := st286_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p489 : ((8534491800403/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT286 (i+1))
      = (∑ i ∈ Finset.range 488, stT286 (i+1)) + stT286 489 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 488
    simpa using h
  have hprev := st286_p488
  have hstep := st286_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p490 : ((17400886078153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT286 (i+1))
      = (∑ i ∈ Finset.range 489, stT286 (i+1)) + stT286 490 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 489
    simpa using h
  have hprev := st286_p489
  have hstep := st286_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p491 : ((713848050043/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT286 (i+1))
      = (∑ i ∈ Finset.range 490, stT286 (i+1)) + stT286 491 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 490
    simpa using h
  have hprev := st286_p490
  have hstep := st286_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p492 : ((3651577416137/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT286 (i+1))
      = (∑ i ∈ Finset.range 491, stT286 (i+1)) + stT286 492 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 491
    simpa using h
  have hprev := st286_p491
  have hstep := st286_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p493 : ((18501082553899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT286 (i+1))
      = (∑ i ∈ Finset.range 492, stT286 (i+1)) + stT286 493 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 492
    simpa using h
  have hprev := st286_p492
  have hstep := st286_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p494 : ((18496981514869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT286 (i+1))
      = (∑ i ∈ Finset.range 493, stT286 (i+1)) + stT286 494 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 493
    simpa using h
  have hprev := st286_p493
  have hstep := st286_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p495 : ((9123927945123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT286 (i+1))
      = (∑ i ∈ Finset.range 494, stT286 (i+1)) + stT286 495 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 494
    simpa using h
  have hprev := st286_p494
  have hstep := st286_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p496 : ((8917669323097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT286 (i+1))
      = (∑ i ∈ Finset.range 495, stT286 (i+1)) + stT286 496 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 495
    simpa using h
  have hprev := st286_p495
  have hstep := st286_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p497 : ((8696591504339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT286 (i+1))
      = (∑ i ∈ Finset.range 496, stT286 (i+1)) + stT286 497 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 496
    simpa using h
  have hprev := st286_p496
  have hstep := st286_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p498 : ((4265908976431/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT286 (i+1))
      = (∑ i ∈ Finset.range 497, stT286 (i+1)) + stT286 498 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 497
    simpa using h
  have hprev := st286_p497
  have hstep := st286_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p499 : ((8475895344329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT286 (i+1))
      = (∑ i ∈ Finset.range 498, stT286 (i+1)) + stT286 499 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 498
    simpa using h
  have hprev := st286_p498
  have hstep := st286_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_p500 : ((8546245526933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT286 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT286 (i+1))
      = (∑ i ∈ Finset.range 499, stT286 (i+1)) + stT286 500 := by
    have h := Finset.sum_range_succ (fun i => stT286 (i+1)) 499
    simpa using h
  have hprev := st286_p499
  have hstep := st286_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st286_s500 :
    |Real.sin (((286 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))
      - ((-474593/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -3126597/10000000) (δ := 1447/100000000) (ψ := 487099/1000000) 286 283
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 286`** (evaluated boundary). -/
theorem station_286_sign : 0 < hardyG ((((286:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 286 500 (by norm_num) (by norm_num)
    ((487099/1000000 : ℚ) : ℝ)
  have hchain := st286_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT286 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((286 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((487099/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st286_c500
  have hsinb := abs_le.mp st286_s500
  have hbdy_lo : ((30330118482261/408981250000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((286 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((487099/1000000 : ℚ) : ℝ))) / 2
          - ((((286:ℕ)):ℝ))
            * Real.sin (((286 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((487099/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((286:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((286:ℝ) * Real.log (500:ℝ) - ((487099/1000000 : ℚ) : ℝ))) / 2
        - ((286:ℝ)) * Real.sin ((286:ℝ) * Real.log (500:ℝ) - ((487099/1000000 : ℚ) : ℝ))
        ≥ ((67820297/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((286:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((67820297/250000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((67820297/250000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((67820297/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((286:ℕ)):ℝ))+1) * (((((286:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((200090922631/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((8546245526933/5000000000000 : ℚ) : ℝ) + ((30330118482261/408981250000000 : ℚ) : ℝ)
      - ((200090922631/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((487099/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((286:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((487099/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((286:ℕ)):ℝ)))).re
      - Real.sin ((487099/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((286:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((286:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((286:ℕ)):ℝ))
      = (((((286:ℕ)):ℝ)) * (Real.log ((((286:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((286:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_286
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
  have hθwin : |(((487099/1000000 : ℚ) : ℝ) + ((64:ℤ)) * (2*Real.pi)) - theta ((((286:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((286:ℕ)):ℝ)))
    (φ := ((487099/1000000 : ℚ) : ℝ) + ((64:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((487099/1000000 : ℚ)) : ℝ) 64).1,
    (cos_sin_shift (((487099/1000000 : ℚ)) : ℝ) 64).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_286_sign
end AxiomAudit
