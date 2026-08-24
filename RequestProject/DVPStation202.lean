import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 202` (rung-217.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT202 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((202 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((118023/125000 : ℚ) : ℝ))

theorem st202_c1 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((146601/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -118023/500000) (δ := 1/1000000000) (ψ := 118023/125000) 202 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t1 : ((293177/500000 : ℚ) : ℝ) ≤ stT202 1 := by
  have hc : ((293177/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((293177/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((293177/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c2 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((166593/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2103659/10000000) (δ := 10159/1000000000) (ψ := 118023/125000) 202 22
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t2 : ((2355803752787/5000000000000 : ℚ) : ℝ) ≤ stT202 2 := by
  have hc : ((333161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2355803752787/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((333161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c3 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((3883/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 665003/2500000) (δ := 10153/1000000000) (ψ := 118023/125000) 202 35
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t3 : ((56040497163/200000000000 : ℚ) : ℝ) ≤ stT202 3 := by
  have hc : ((19413/40000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56040497163/200000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((19413/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c4 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-870553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6567803/10000000) (δ := 10117/1000000000) (ψ := 118023/125000) 202 44
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t4 : ((-4353015870603/10000000000000 : ℚ) : ℝ) ≤ stT202 4 := by
  have hc : ((-870603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4353015870603/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-870603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c5 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-837427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1281677/2000000) (δ := 407/40000000) (ψ := 118023/125000) 202 52
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t5 : ((-468163880109/1250000000000 : ℚ) : ℝ) ≤ stT202 5 := by
  have hc : ((-837477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-468163880109/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-837477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c6 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-95769/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1781039/2500000) (δ := 10111/1000000000) (ψ := 118023/125000) 202 57
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t6 : ((-195497863421/500000000000 : ℚ) : ℝ) ≤ stT202 6 := by
  have hc : ((-47887/50000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195497863421/500000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-47887/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c7 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-105277/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6430443/10000000) (δ := 2539/250000000) (ψ := 118023/125000) 202 62
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t7 : ((-318346647557/1000000000000 : ℚ) : ℝ) ≤ stT202 7 := by
  have hc : ((-421133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-318346647557/1000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-421133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c8 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-73787/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -292251/625000) (δ := 10183/1000000000) (ψ := 118023/125000) 202 67
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t8 : ((-260920641433/2500000000000 : ℚ) : ℝ) ≤ stT202 8 := by
  have hc : ((-147599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-260920641433/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-147599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c9 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-498797/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7680509/10000000) (δ := 1263/125000000) (ψ := 118023/125000) 202 70
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t9 : ((-415685083137/1250000000000 : ℚ) : ℝ) ≤ stT202 9 := by
  have hc : ((-249411/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-415685083137/1250000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-249411/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c10 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((712517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -486073/2500000) (δ := 1027/100000000) (ψ := 118023/125000) 202 74
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t10 : ((2253018007359/10000000000000 : ℚ) : ℝ) ≤ stT202 10 := by
  have hc : ((712467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2253018007359/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((712467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c11 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((18613/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -93653/1000000) (δ := 5127/500000000) (ψ := 118023/125000) 202 77
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t11 : ((14029320789/50000000000 : ℚ) : ℝ) ≤ stT202 11 := by
  have hc : ((4653/5000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14029320789/50000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((4653/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c12 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-76993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4119663/10000000) (δ := 159/15625000) (ψ := 118023/125000) 202 80
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t12 : ((-6950126073/312500000000 : ℚ) : ℝ) ≤ stT202 12 := by
  have hc : ((-77043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6950126073/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-77043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c13 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-74851/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2442987/5000000) (δ := 1019/100000000) (ψ := 118023/125000) 202 82
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t13 : ((-207627058361/2000000000000 : ℚ) : ℝ) ≤ stT202 13 := by
  have hc : ((-74861/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207627058361/2000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-74861/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c14 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-86793/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -75209/156250) (δ := 79/7812500) (ψ := 118023/125000) 202 85
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t14 : ((-463995015543/5000000000000 : ℚ) : ℝ) ≤ stT202 14 := by
  have hc : ((-173611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-463995015543/5000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-173611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c15 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((849819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -86743/625000) (δ := 5063/500000000) (ψ := 118023/125000) 202 87
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t15 : ((548523340193/2500000000000 : ℚ) : ℝ) ≤ stT202 15 := by
  have hc : ((849769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((548523340193/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((849769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c16 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((996411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6621/312500) (δ := 507/50000000) (ψ := 118023/125000) 202 89
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t16 : ((996361/4000000 : ℚ) : ℝ) ≤ stT202 16 := by
  have hc : ((996361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((996361/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((996361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c17 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((459561/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -126547/1250000) (δ := 1281/125000000) (ψ := 118023/125000) 202 91
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t17 : ((17414662419/78125000000 : ℚ) : ℝ) ≤ stT202 17 := by
  have hc : ((28721/31250 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17414662419/78125000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((28721/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c18 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((453/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -356331/1000000) (δ := 10169/1000000000) (ψ := 118023/125000) 202 93
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t18 : ((17077802901/500000000000 : ℚ) : ℝ) ≤ stT202 18 := by
  have hc : ((14491/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17077802901/500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((14491/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c19 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-997447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7675301/10000000) (δ := 10219/1000000000) (ψ := 118023/125000) 202 95
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t19 : ((-1144207861263/5000000000000 : ℚ) : ℝ) ≤ stT202 19 := by
  have hc : ((-997497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1144207861263/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-997497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c20 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((533603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2519853/10000000) (δ := 10291/1000000000) (ψ := 118023/125000) 202 96
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t20 : ((1193060256051/10000000000000 : ℚ) : ℝ) ≤ stT202 20 := by
  have hc : ((533553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1193060256051/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((533553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c21 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-13163/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4257023/10000000) (δ := 2021/200000000) (ψ := 118023/125000) 202 98
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t21 : ((-1795933317/62500000000 : ℚ) : ℝ) ≤ stT202 21 := by
  have hc : ((-823/6250 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1795933317/62500000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-823/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c22 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((4971/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1763807/5000000) (δ := 2553/250000000) (ψ := 118023/125000) 202 99
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t22 : ((169518008577/5000000000000 : ℚ) : ℝ) ≤ stT202 22 := by
  have hc : ((79511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169518008577/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((79511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c23 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-28449/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2720077/5000000) (δ := 159/15625000) (ψ := 118023/125000) 202 101
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t23 : ((-23730201187/200000000000 : ℚ) : ℝ) ≤ stT202 23 := by
  have hc : ((-56903/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23730201187/200000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-56903/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c24 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((495261/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 344481/10000000) (δ := 5067/500000000) (ψ := 118023/125000) 202 102
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t24 : ((252724006969/1250000000000 : ℚ) : ℝ) ≤ stT202 24 := by
  have hc : ((123809/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252724006969/1250000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((123809/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c25 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-7897/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1312907/2500000) (δ := 10241/1000000000) (ψ := 118023/125000) 202 103
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t25 : ((-505458252729/5000000000000 : ℚ) : ℝ) ≤ stT202 25 := by
  have hc : ((-252729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-505458252729/5000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-252729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c26 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-826207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1271569/2000000) (δ := 2051/200000000) (ψ := 118023/125000) 202 105
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t26 : ((-810211915317/5000000000000 : ℚ) : ℝ) ≤ stT202 26 := by
  have hc : ((-826257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-810211915317/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-826257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c27 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((359763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3006957/10000000) (δ := 10163/1000000000) (ψ := 118023/125000) 202 106
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t27 : ((1384535337/20000000000 : ℚ) : ℝ) ≤ stT202 27 := by
  have hc : ((359713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1384535337/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((359713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c28 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((990259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21827/625000) (δ := 10133/1000000000) (ψ := 118023/125000) 202 107
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t28 : ((935659376399/5000000000000 : ℚ) : ℝ) ≤ stT202 28 := by
  have hc : ((990209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((935659376399/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((990209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c29 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((98321/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1663911/10000000) (δ := 5113/500000000) (ψ := 118023/125000) 202 108
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t29 : ((730263479827/5000000000000 : ℚ) : ℝ) ≤ stT202 29 := by
  have hc : ((393259/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((730263479827/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((393259/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c30 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((333783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1538103/5000000) (δ := 2571/250000000) (ψ := 118023/125000) 202 109
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t30 : ((609310021153/10000000000000 : ℚ) : ℝ) ≤ stT202 30 := by
  have hc : ((333733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((609310021153/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((333733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c31 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-3/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1963571/5000000) (δ := 10191/1000000000) (ψ := 118023/125000) 202 110
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t31 : ((-9878297/500000000000 : ℚ) : ℝ) ≤ stT202 31 := by
  have hc : ((-11/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9878297/500000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-11/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c32 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-64873/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 265767/625000) (δ := 2021/200000000) (ψ := 118023/125000) 202 111
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t32 : ((-57362271383/2500000000000 : ℚ) : ℝ) ≤ stT202 32 := by
  have hc : ((-32449/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57362271383/2500000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-32449/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c33 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-62749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4083967/10000000) (δ := 5103/500000000) (ψ := 118023/125000) 202 112
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t33 : ((-109319054823/10000000000000 : ℚ) : ℝ) ≤ stT202 33 := by
  have hc : ((-62799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109319054823/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-62799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c34 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((94473/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 431471/1250000) (δ := 1029/100000000) (ψ := 118023/125000) 202 113
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t34 : ((2024711291/62500000000 : ℚ) : ℝ) ≤ stT202 34 := by
  have hc : ((5903/31250 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2024711291/62500000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((5903/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c35 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((579243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2382493/10000000) (δ := 511/50000000) (ψ := 118023/125000) 202 114
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t35 : ((244753640361/2500000000000 : ℚ) : ℝ) ≤ stT202 35 := by
  have hc : ((579193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((244753640361/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((579193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c36 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((935779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 450417/5000000) (δ := 10127/1000000000) (ψ := 118023/125000) 202 115
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t36 : ((779773854757/5000000000000 : ℚ) : ℝ) ≤ stT202 36 := by
  have hc : ((935729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((779773854757/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((935729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c37 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((231393/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -485317/5000000) (δ := 5117/500000000) (ψ := 118023/125000) 202 116
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t37 : ((760773993629/5000000000000 : ℚ) : ℝ) ≤ stT202 37 := by
  have hc : ((462761/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((760773993629/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((462761/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c38 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((282437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3211157/10000000) (δ := 10261/1000000000) (ψ := 118023/125000) 202 117
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t38 : ((229046072409/5000000000000 : ℚ) : ℝ) ≤ stT202 38 := by
  have hc : ((282387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229046072409/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((282387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c39 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-681493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1450373/2500000) (δ := 10249/1000000000) (ψ := 118023/125000) 202 118
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t39 : ((-545671269063/5000000000000 : ℚ) : ℝ) ≤ stT202 39 := by
  have hc : ((-681543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-545671269063/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-681543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c40 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-940059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6983997/10000000) (δ := 10249/1000000000) (ψ := 118023/125000) 202 118
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t40 : ((-1486443004151/10000000000000 : ℚ) : ℝ) ≤ stT202 40 := by
  have hc : ((-940109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1486443004151/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-940109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c41 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((36207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 936449/2500000) (δ := 10247/1000000000) (ψ := 118023/125000) 202 119
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t41 : ((28253384067/2500000000000 : ℚ) : ℝ) ≤ stT202 41 := by
  have hc : ((18091/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28253384067/2500000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((18091/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c42 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((99657/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 207121/10000000) (δ := 507/50000000) (ψ := 118023/125000) 202 120
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t42 : ((38441581129/250000000000 : ℚ) : ℝ) ≤ stT202 42 := by
  have hc : ((24913/25000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38441581129/250000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((24913/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c43 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((61653/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -180897/500000) (δ := 10233/1000000000) (ψ := 118023/125000) 202 121
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t43 : ((4699088779/250000000000 : ℚ) : ℝ) ≤ stT202 43 := by
  have hc : ((15407/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4699088779/250000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((15407/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c44 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-499241/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1543241/2000000) (δ := 10277/1000000000) (ψ := 118023/125000) 202 122
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t44 : ((-376335976581/2500000000000 : ℚ) : ℝ) ≤ stT202 44 := by
  have hc : ((-249633/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-376335976581/2500000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-249633/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c45 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((117501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3632559/10000000) (δ := 10277/1000000000) (ψ := 118023/125000) 202 122
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t45 : ((175085497661/10000000000000 : ℚ) : ℝ) ≤ stT202 45 := by
  have hc : ((117451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175085497661/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((117451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c46 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((231187/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48803/500000) (δ := 2037/200000000) (ψ := 118023/125000) 202 123
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t46 : ((681696150231/5000000000000 : ℚ) : ℝ) ≤ stT202 46 := by
  have hc : ((462349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((681696150231/5000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((462349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c47 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-687863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2911671/5000000) (δ := 10111/1000000000) (ψ := 118023/125000) 202 124
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t47 : ((-20068485949/200000000000 : ℚ) : ℝ) ≤ stT202 47 := by
  have hc : ((-687913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20068485949/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-687913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c48 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-345389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38469/80000) (δ := 10111/1000000000) (ψ := 118023/125000) 202 124
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t48 : ((-31162397629/625000000000 : ℚ) : ℝ) ≤ stT202 48 := by
  have hc : ((-345439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31162397629/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-345439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c49 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((490557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -243321/5000000) (δ := 10199/1000000000) (ψ := 118023/125000) 202 125
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t49 : ((175189947443/1250000000000 : ℚ) : ℝ) ≤ stT202 49 := by
  have hc : ((122633/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175189947443/1250000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((122633/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c50 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-735281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46814/78125) (δ := 10297/1000000000) (ψ := 118023/125000) 202 126
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t50 : ((-519957697417/5000000000000 : ℚ) : ℝ) ≤ stT202 50 := by
  have hc : ((-735331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-519957697417/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-735331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c51 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-16223/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4008121/10000000) (δ := 10297/1000000000) (ψ := 118023/125000) 202 126
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t51 : ((-2843970711/625000000000 : ℚ) : ℝ) ≤ stT202 51 := by
  have hc : ((-2031/62500 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2843970711/625000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-2031/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c52 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((72657/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1893701/10000000) (δ := 10213/1000000000) (ψ := 118023/125000) 202 127
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t52 : ((100750161/1000000000 : ℚ) : ℝ) ≤ stT202 52 := by
  have hc : ((18163/25000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100750161/1000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((18163/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c53 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-998683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 193141/250000) (δ := 10213/1000000000) (ψ := 118023/125000) 202 127
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t53 : ((-685932820599/5000000000000 : ℚ) : ℝ) ≤ stT202 53 := by
  have hc : ((-998733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-685932820599/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-998733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c54 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((208721/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1457187/10000000) (δ := 253/25000000) (ψ := 118023/125000) 202 128
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t54 : ((568032323859/5000000000000 : ℚ) : ℝ) ≤ stT202 54 := by
  have hc : ((417417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((568032323859/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((417417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c55 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-205247/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4984481/10000000) (δ := 407/40000000) (ψ := 118023/125000) 202 129
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t55 : ((-86496489/1562500000 : ℚ) : ℝ) ≤ stT202 55 := by
  have hc : ((-25659/62500 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86496489/1562500000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-25659/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c56 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-37539/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2057431/5000000) (δ := 2557/250000000) (ψ := 118023/125000) 202 129
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t56 : ((-12549259037/1250000000000 : ℚ) : ℝ) ≤ stT202 56 := by
  have hc : ((-9391/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12549259037/1250000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-9391/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c57 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((97439/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -663701/2500000) (δ := 2567/250000000) (ψ := 118023/125000) 202 130
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t57 : ((32261957057/500000000000 : ℚ) : ℝ) ≤ stT202 57 := by
  have hc : ((97429/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32261957057/500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((97429/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c58 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-77101/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1225611/2000000) (δ := 2567/250000000) (ψ := 118023/125000) 202 130
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t58 : ((-10124518989/100000000000 : ℚ) : ℝ) ≤ stT202 58 := by
  have hc : ((-38553/50000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10124518989/100000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-38553/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c59 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((464537/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -236809/2500000) (δ := 10161/1000000000) (ψ := 118023/125000) 202 131
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t59 : ((4724555181/39062500000 : ℚ) : ℝ) ≤ stT202 59 := by
  have hc : ((14516/15625 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4724555181/39062500000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((14516/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c60 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-992141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 150807/200000) (δ := 5121/500000000) (ψ := 118023/125000) 202 131
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t60 : ((-256182724009/2000000000000 : ℚ) : ℝ) ≤ stT202 60 := by
  have hc : ((-992191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-256182724009/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-992191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c61 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((498709/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 179683/10000000) (δ := 10149/1000000000) (ψ := 118023/125000) 202 132
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t61 : ((9976547433/78125000000 : ℚ) : ℝ) ≤ stT202 61 := by
  have hc : ((124671/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9976547433/78125000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((124671/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c62 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-976997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -914591/1250000) (δ := 10147/1000000000) (ψ := 118023/125000) 202 133
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t62 : ((-620425822047/5000000000000 : ℚ) : ℝ) ≤ stT202 62 := by
  have hc : ((-977047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-620425822047/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-977047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c63 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((95373/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 381737/5000000) (δ := 10147/1000000000) (ψ := 118023/125000) 202 133
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t63 : ((15019041401/125000000000 : ℚ) : ℝ) ≤ stT202 63 := by
  have hc : ((11921/12500 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15019041401/125000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((11921/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c64 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-941091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3495799/5000000) (δ := 10239/1000000000) (ψ := 118023/125000) 202 134
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t64 : ((-1176427191141/10000000000000 : ℚ) : ℝ) ≤ stT202 64 := by
  have hc : ((-941141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1176427191141/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-941141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c65 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((472171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 838023/10000000) (δ := 10239/1000000000) (ψ := 118023/125000) 202 134
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t65 : ((292812437331/2500000000000 : ℚ) : ℝ) ≤ stT202 65 := by
  have hc : ((236073/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((292812437331/2500000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((236073/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c66 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-480851/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1789963/2500000) (δ := 10271/1000000000) (ψ := 118023/125000) 202 135
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t66 : ((-29595874077/250000000000 : ℚ) : ℝ) ≤ stT202 66 := by
  have hc : ((-120219/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29595874077/250000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-120219/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c67 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((984949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 434287/10000000) (δ := 2533/250000000) (ψ := 118023/125000) 202 135
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t67 : ((601622599453/5000000000000 : ℚ) : ℝ) ≤ stT202 67 := by
  have hc : ((984899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((601622599453/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((984899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c68 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-999693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7792051/10000000) (δ := 409/40000000) (ψ := 118023/125000) 202 136
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t68 : ((-1212367341497/10000000000000 : ℚ) : ℝ) ≤ stT202 68 := by
  have hc : ((-999743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1212367341497/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-999743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c69 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((123243/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -419657/10000000) (δ := 409/40000000) (ψ := 118023/125000) 202 136
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t69 : ((296719094763/2500000000000 : ℚ) : ℝ) ≤ stT202 69 := by
  have hc : ((492947/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((296719094763/2500000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((492947/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c70 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-919913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6846637/10000000) (δ := 5089/500000000) (ψ := 118023/125000) 202 136
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t70 : ((-1099566456527/10000000000000 : ℚ) : ℝ) ≤ stT202 70 := by
  have hc : ((-919963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1099566456527/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-919963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c71 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((15561/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1698103/10000000) (δ := 2057/200000000) (ψ := 118023/125000) 202 137
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t71 : ((461657809/5000000000 : ℚ) : ℝ) ≤ stT202 71 := by
  have hc : ((389/500 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((461657809/5000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((389/500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c72 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-271999/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2682489/5000000) (δ := 5059/500000000) (ψ := 118023/125000) 202 137
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t72 : ((-2504558971/39062500000 : ℚ) : ℝ) ≤ stT202 72 := by
  have hc : ((-34003/62500 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2504558971/39062500000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-34003/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c73 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((109041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3377369/10000000) (δ := 10211/1000000000) (ψ := 118023/125000) 202 138
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t73 : ((15949190697/625000000000 : ℚ) : ℝ) ≤ stT202 73 := by
  have hc : ((13627/62500 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15949190697/625000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((13627/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c74 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((34509/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3493459/10000000) (δ := 10211/1000000000) (ψ := 118023/125000) 202 138
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t74 : ((10026064881/500000000000 : ℚ) : ℝ) ≤ stT202 74 := by
  have hc : ((34499/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10026064881/500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((34499/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c75 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-14189/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2717919/5000000) (δ := 10299/1000000000) (ψ := 118023/125000) 202 139
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t75 : ((-65541983461/1000000000000 : ℚ) : ℝ) ≤ stT202 75 := by
  have hc : ((-56761/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65541983461/1000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-56761/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c76 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((877009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 313247/2500000) (δ := 10299/1000000000) (ψ := 118023/125000) 202 139
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t76 : ((502970187901/5000000000000 : ℚ) : ℝ) ≤ stT202 76 := by
  have hc : ((876959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((502970187901/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((876959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c77 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1570713/2000000) (δ := 10207/1000000000) (ψ := 118023/125000) 202 140
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t77 : ((-11396629803/100000000000 : ℚ) : ℝ) ≤ stT202 77 := by
  have hc : ((-20001/20000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11396629803/100000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-20001/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c78 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((8603/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -334337/2500000) (δ := 10207/1000000000) (ψ := 118023/125000) 202 140
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t78 : ((3896165157/40000000000 : ℚ) : ℝ) ≤ stT202 78 := by
  have hc : ((3441/4000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3896165157/40000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((3441/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c79 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-225347/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5095847/10000000) (δ := 10207/1000000000) (ψ := 118023/125000) 202 140
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t79 : ((-1980963537/39062500000 : ℚ) : ℝ) ≤ stT202 79 := by
  have hc : ((-56343/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1980963537/39062500000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-56343/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c80 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-6637/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4259823/10000000) (δ := 10289/1000000000) (ψ := 118023/125000) 202 141
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t80 : ((-7423186743/500000000000 : ℚ) : ℝ) ≤ stT202 80 := by
  have hc : ((-13279/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7423186743/500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-13279/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c81 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((692811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 100677/500000) (δ := 5057/500000000) (ψ := 118023/125000) 202 141
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t81 : ((769734367471/10000000000000 : ℚ) : ℝ) ≤ stT202 81 := by
  have hc : ((692761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((769734367471/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((692761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c82 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-989881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7498023/10000000) (δ := 5091/500000000) (ψ := 118023/125000) 202 142
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t82 : ((-273299160549/2500000000000 : ℚ) : ℝ) ≤ stT202 82 := by
  have hc : ((-989931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-273299160549/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-989931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c83 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((426083/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -344179/2500000) (δ := 5091/500000000) (ψ := 118023/125000) 202 142
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t83 : ((116914788809/1250000000000 : ℚ) : ℝ) ≤ stT202 83 := by
  have hc : ((213029/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116914788809/1250000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((213029/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c84 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-146661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 116781/250000) (δ := 20221/1000000000) (ψ := 118023/125000) 202 142
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t84 : ((-8002381387/250000000000 : ℚ) : ℝ) ≤ stT202 84 := by
  have hc : ((-73343/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8002381387/250000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-73343/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c85 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-87593/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2530163/5000000) (δ := 633/62500000) (ψ := 118023/125000) 202 143
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t85 : ((-95018856759/2000000000000 : ℚ) : ℝ) ≤ stT202 85 := by
  have hc : ((-87603/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95018856759/2000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-87603/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c86 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((943267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 423077/5000000) (δ := 633/62500000) (ψ := 118023/125000) 202 143
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t86 : ((1017096357959/10000000000000 : ℚ) : ℝ) ≤ stT202 86 := by
  have hc : ((943217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1017096357959/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((943217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c87 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-892549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 835551/1250000) (δ := 411/40000000) (ψ := 118023/125000) 202 143
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t87 : ((-956966991687/10000000000000 : ℚ) : ℝ) ≤ stT202 87 := by
  have hc : ((-892599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-956966991687/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-892599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c88 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((16669/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3252061/10000000) (δ := 2047/200000000) (ψ := 118023/125000) 202 144
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t88 : ((142126981981/5000000000000 : ℚ) : ℝ) ≤ stT202 88 := by
  have hc : ((133327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142126981981/5000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((133327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c89 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((555631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1227093/5000000) (δ := 1271/125000000) (ψ := 118023/125000) 202 144
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t89 : ((588914193257/10000000000000 : ℚ) : ℝ) ≤ stT202 89 := by
  have hc : ((555581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((588914193257/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((555581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c90 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-995291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7611261/10000000) (δ := 513/50000000) (ψ := 118023/125000) 202 145
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t90 : ((-1049181980713/10000000000000 : ℚ) : ℝ) ≤ stT202 90 := by
  have hc : ((-995341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1049181980713/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-995341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c91 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((687733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1015543/5000000) (δ := 20343/1000000000) (ψ := 118023/125000) 202 145
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t91 : ((180221771493/2500000000000 : ℚ) : ℝ) ≤ stT202 91 := by
  have hc : ((687683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180221771493/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((687683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c92 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((87331/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 872021/2500000) (δ := 10143/1000000000) (ψ := 118023/125000) 202 145
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t92 : ((11377848879/625000000000 : ℚ) : ℝ) ≤ stT202 92 := by
  have hc : ((43653/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11377848879/625000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((43653/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c93 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-452919/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54083/80000) (δ := 10153/1000000000) (ψ := 118023/125000) 202 146
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t93 : ((-3669384271/39062500000 : ℚ) : ℝ) ≤ stT202 93 := by
  have hc : ((-28309/31250 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3669384271/39062500000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-28309/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c94 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((855801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -84953/625000) (δ := 41/4000000) (ψ := 118023/125000) 202 146
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t94 : ((882639552171/10000000000000 : ℚ) : ℝ) ≤ stT202 94 := by
  have hc : ((855751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((882639552171/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((855751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c95 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-11543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 498089/1250000) (δ := 10153/1000000000) (ψ := 118023/125000) 202 146
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t95 : ((-741782817/312500000000 : ℚ) : ℝ) ≤ stT202 95 := by
  have hc : ((-723/31250 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-741782817/312500000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-723/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c96 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-3373/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1287049/2000000) (δ := 5123/500000000) (ψ := 118023/125000) 202 147
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t96 : ((-8606896893/100000000000 : ℚ) : ℝ) ≤ stT202 96 := by
  have hc : ((-8433/10000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8606896893/100000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-8433/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c97 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((886619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1202031/10000000) (δ := 5123/500000000) (ψ := 118023/125000) 202 147
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t97 : ((450087143937/5000000000000 : ℚ) : ℝ) ≤ stT202 97 := by
  have hc : ((886569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((450087143937/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((886569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c98 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-20203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1988751/5000000) (δ := 10157/1000000000) (ψ := 118023/125000) 202 147
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t98 : ((-20458628709/10000000000000 : ℚ) : ℝ) ≤ stT202 98 := by
  have hc : ((-20253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20458628709/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-20253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c99 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-87749/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6603499/10000000) (δ := 1283/125000000) (ψ := 118023/125000) 202 148
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t99 : ((-22049026163/250000000000 : ℚ) : ℝ) ≤ stT202 99 := by
  have hc : ((-43877/50000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22049026163/250000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-43877/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c100 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((818937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -764049/5000000) (δ := 10139/1000000000) (ψ := 118023/125000) 202 148
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t100 : ((818886181113/10000000000000 : ℚ) : ℝ) ≤ stT202 100 := by
  have hc : ((818887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((818886181113/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((818887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c101 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((171207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1748427/5000000) (δ := 10139/1000000000) (ψ := 118023/125000) 202 148
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t101 : ((170307547809/10000000000000 : ℚ) : ℝ) ≤ stT202 101 := by
  have hc : ((171157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170307547809/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((171157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c102 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-484787/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3617849/5000000) (δ := 1279/125000000) (ψ := 118023/125000) 202 149
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t102 : ((-30002227011/312500000000 : ℚ) : ℝ) ≤ stT202 102 := by
  have hc : ((-121203/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30002227011/312500000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-121203/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c103 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((120599/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2308867/10000000) (δ := 10171/1000000000) (ψ := 118023/125000) 202 149
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t103 : ((118819838781/2000000000000 : ℚ) : ℝ) ≤ stT202 103 := by
  have hc : ((120589/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118819838781/2000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((120589/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c104 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((258199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 321299/1250000) (δ := 1279/125000000) (ψ := 118023/125000) 202 149
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t104 : ((6329006523/125000000000 : ℚ) : ℝ) ≤ stT202 104 := by
  have hc : ((129087/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6329006523/125000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((129087/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c105 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-983773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 740299/1000000) (δ := 10171/1000000000) (ψ := 118023/125000) 202 149
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t105 : ((-960113849523/10000000000000 : ℚ) : ℝ) ≤ stT202 105 := by
  have hc : ((-983823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-960113849523/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-983823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c106 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((162777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -351823/1000000) (δ := 81/8000000) (ψ := 118023/125000) 202 150
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t106 : ((31610858839/2000000000000 : ℚ) : ℝ) ≤ stT202 106 := by
  have hc : ((162727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31610858839/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((162727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c107 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((882593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1223619/10000000) (δ := 81/8000000) (ψ := 118023/125000) 202 150
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t107 : ((53324130603/625000000000 : ℚ) : ℝ) ≤ stT202 107 := by
  have hc : ((882543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53324130603/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((882543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c108 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-715777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5921331/10000000) (δ := 81/8000000) (ψ := 118023/125000) 202 150
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t108 : ((-688805246577/10000000000000 : ℚ) : ℝ) ≤ stT202 108 := by
  have hc : ((-715827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-688805246577/10000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-715827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c109 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-115911/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5132249/10000000) (δ := 5093/500000000) (ψ := 118023/125000) 202 151
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t109 : ((-222069316469/5000000000000 : ℚ) : ℝ) ≤ stT202 109 := by
  have hc : ((-231847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222069316469/5000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-231847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c110 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((489209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -520337/10000000) (δ := 10217/1000000000) (ψ := 118023/125000) 202 151
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t110 : ((7287786797/78125000000 : ℚ) : ℝ) ≤ stT202 110 := by
  have hc : ((15287/15625 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7287786797/78125000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((15287/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c111 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-49129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4049863/10000000) (δ := 5093/500000000) (ψ := 118023/125000) 202 151
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t111 : ((-23339320641/5000000000000 : ℚ) : ℝ) ≤ stT202 111 := by
  have hc : ((-49179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23339320641/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-49179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c112 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-958241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7128957/10000000) (δ := 10293/1000000000) (ψ := 118023/125000) 202 152
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t112 : ((-56593791587/625000000000 : ℚ) : ℝ) ≤ stT202 112 := by
  have hc : ((-958291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56593791587/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-958291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c113 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((492353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -660003/2500000) (δ := 10293/1000000000) (ψ := 118023/125000) 202 152
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t113 : ((5788990977/125000000000 : ℚ) : ℝ) ≤ stT202 113 := by
  have hc : ((492303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5788990977/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((492303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c114 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((749337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1809341/10000000) (δ := 10293/1000000000) (ψ := 118023/125000) 202 152
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t114 : ((140354192979/2000000000000 : ℚ) : ℝ) ≤ stT202 114 := by
  have hc : ((749287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140354192979/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((749287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c115 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-79387/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6219859/10000000) (δ := 1011/100000000) (ψ := 118023/125000) 202 152
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t115 : ((-462708981/6250000000 : ℚ) : ℝ) ≤ stT202 115 := by
  have hc : ((-2481/3125 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-462708981/6250000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-2481/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c116 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-457809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2557907/5000000) (δ := 51/5000000) (ψ := 118023/125000) 202 153
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t116 : ((-425111550743/10000000000000 : ℚ) : ℝ) ≤ stT202 116 := by
  have hc : ((-457859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-425111550743/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-457859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c117 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((951599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -156199/2000000) (δ := 51/5000000) (ψ := 118023/125000) 202 153
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t117 : ((1759414101/20000000000 : ℚ) : ℝ) ≤ stT202 117 := by
  have hc : ((951549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1759414101/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((951549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c118 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((163299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 879227/2500000) (δ := 10203/1000000000) (ψ := 118023/125000) 202 153
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t118 : ((75141392463/5000000000000 : ℚ) : ℝ) ≤ stT202 118 := by
  have hc : ((163249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75141392463/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((163249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c119 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-124943/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3889251/5000000) (δ := 10203/1000000000) (ψ := 118023/125000) 202 153
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t119 : ((-458163410103/5000000000000 : ℚ) : ℝ) ≤ stT202 119 := by
  have hc : ((-499797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-458163410103/5000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-499797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c120 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((89289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -370347/1000000) (δ := 1287/125000000) (ψ := 118023/125000) 202 154
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t120 : ((8146360593/1000000000000 : ℚ) : ℝ) ≤ stT202 120 := by
  have hc : ((89239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8146360593/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((89239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c121 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((490527/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3808/78125) (δ := 1287/125000000) (ψ := 118023/125000) 202 154
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t121 : ((22295523159/250000000000 : ℚ) : ℝ) ≤ stT202 121 := by
  have hc : ((245251/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22295523159/250000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((245251/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c122 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-141411/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4643827/10000000) (δ := 10107/1000000000) (ψ := 118023/125000) 202 154
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t122 : ((-16006276761/625000000000 : ℚ) : ℝ) ≤ stT202 122 := by
  have hc : ((-35359/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16006276761/625000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-35359/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c123 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-934151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -694167/1000000) (δ := 10189/1000000000) (ψ := 118023/125000) 202 155
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t123 : ((-84234101567/1000000000000 : ℚ) : ℝ) ≤ stT202 123 := by
  have hc : ((-934201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84234101567/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-934201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c124 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((83331/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -356573/1250000) (δ := 10189/1000000000) (ψ := 118023/125000) 202 155
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t124 : ((37412212173/1000000000000 : ℚ) : ℝ) ≤ stT202 124 := by
  have hc : ((83321/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37412212173/1000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((83321/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c125 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((177263/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1203677/10000000) (δ := 10189/1000000000) (ψ := 118023/125000) 202 155
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t125 : ((158539869031/2000000000000 : ℚ) : ℝ) ≤ stT202 125 := by
  have hc : ((177253/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158539869031/2000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((177253/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c126 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-248549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2613809/5000000) (δ := 10189/1000000000) (ψ := 118023/125000) 202 155
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t126 : ((-110723683977/2500000000000 : ℚ) : ℝ) ≤ stT202 126 := by
  have hc : ((-124287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110723683977/2500000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-124287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c127 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-854461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -648827/1000000) (δ := 10281/1000000000) (ψ := 118023/125000) 202 156
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t127 : ((-758256317427/10000000000000 : ℚ) : ℝ) ≤ stT202 127 := by
  have hc : ((-854511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-758256317427/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-854511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c128 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((531029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1263727/5000000) (δ := 10281/1000000000) (ψ := 118023/125000) 202 156
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t128 : ((469323311457/10000000000000 : ℚ) : ℝ) ≤ stT202 128 := by
  have hc : ((530979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((469323311457/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((530979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c129 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((846711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1402557/10000000) (δ := 10281/1000000000) (ψ := 118023/125000) 202 156
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t129 : ((14908853549/200000000000 : ℚ) : ℝ) ≤ stT202 129 := by
  have hc : ((846661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14908853549/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((846661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c130 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-522747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5302167/10000000) (δ := 10281/1000000000) (ψ := 118023/125000) 202 156
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t130 : ((-458523814023/10000000000000 : ℚ) : ℝ) ≤ stT202 130 := by
  have hc : ((-522797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-458523814023/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-522797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c131 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-864229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6536031/10000000) (δ := 10229/1000000000) (ψ := 118023/125000) 202 157
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t131 : ((-151024976739/2000000000000 : ℚ) : ℝ) ≤ stT202 131 := by
  have hc : ((-864279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151024976739/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-864279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c132 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((236421/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -673927/2500000) (δ := 10229/1000000000) (ψ := 118023/125000) 202 157
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t132 : ((12859765103/312500000000 : ℚ) : ℝ) ≤ stT202 132 := by
  have hc : ((59099/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12859765103/312500000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((59099/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c133 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((902071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 278907/2500000) (δ := 10229/1000000000) (ψ := 118023/125000) 202 157
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t133 : ((782150527289/10000000000000 : ℚ) : ℝ) ≤ stT202 133 := by
  have hc : ((902021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((782150527289/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((902021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c134 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-189431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2449203/5000000) (δ := 20229/1000000000) (ψ := 118023/125000) 202 157
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t134 : ((-10229072829/312500000000 : ℚ) : ℝ) ≤ stT202 134 := by
  have hc : ((-11841/31250 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10229072829/312500000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-11841/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c135 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-118669/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1763727/2500000) (δ := 10267/1000000000) (ψ := 118023/125000) 202 158
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t135 : ((-408557586763/5000000000000 : ℚ) : ℝ) ≤ stT202 135 := by
  have hc : ((-474701/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-408557586763/5000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-474701/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c136 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((237327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3327957/10000000) (δ := 1267/125000000) (ψ := 118023/125000) 202 158
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t136 : ((50865782321/2500000000000 : ℚ) : ℝ) ≤ stT202 136 := by
  have hc : ((237277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50865782321/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((237277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c137 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((494483/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 371723/10000000) (δ := 10267/1000000000) (ψ := 118023/125000) 202 158
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t137 : ((211221826753/2500000000000 : ℚ) : ℝ) ≤ stT202 137 := by
  have hc : ((247229/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211221826753/2500000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((247229/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c138 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-46961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4044437/10000000) (δ := 1267/125000000) (ψ := 118023/125000) 202 158
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t138 : ((-40018442827/10000000000000 : ℚ) : ℝ) ≤ stT202 138 := by
  have hc : ((-47011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40018442827/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-47011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c139 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-249467/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 120167/156250) (δ := 10267/1000000000) (ψ := 118023/125000) 202 158
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t139 : ((-423211535251/5000000000000 : ℚ) : ℝ) ≤ stT202 139 := by
  have hc : ((-498959/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-423211535251/5000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-498959/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c140 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-18697/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2198591/5000000) (δ := 10243/1000000000) (ψ := 118023/125000) 202 159
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t140 : ((-1580608881/100000000000 : ℚ) : ℝ) ≤ stT202 140 := by
  have hc : ((-9351/50000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1580608881/100000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-9351/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c141 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((948871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -160579/2000000) (δ := 10243/1000000000) (ψ := 118023/125000) 202 159
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t141 : ((799050553971/10000000000000 : ℚ) : ℝ) ≤ stT202 141 := by
  have hc : ((948821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((799050553971/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((948821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c142 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((111967/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2766041/10000000) (δ := 10243/1000000000) (ψ := 118023/125000) 202 159
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t142 : ((187900178529/5000000000000 : ℚ) : ℝ) ≤ stT202 142 := by
  have hc : ((223909/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187900178529/5000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((223909/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c143 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-407629/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6309929/10000000) (δ := 10243/1000000000) (ψ := 118023/125000) 202 159
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t143 : ((-170448901961/2500000000000 : ℚ) : ℝ) ≤ stT202 143 := by
  have hc : ((-203827/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170448901961/2500000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-203827/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c144 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-35191/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1469723/2500000) (δ := 10253/1000000000) (ψ := 118023/125000) 202 160
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t144 : ((-29327940129/500000000000 : ℚ) : ℝ) ≤ stT202 144 := by
  have hc : ((-70387/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29327940129/500000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-70387/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c145 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((289369/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2384039/10000000) (δ := 203/20000000) (ψ := 118023/125000) 202 160
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t145 : ((1877241267/39062500000 : ℚ) : ℝ) ≤ stT202 145 := by
  have hc : ((9042/15625 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1877241267/39062500000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((9042/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c146 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((56687/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 43471/400000) (δ := 10253/1000000000) (ψ := 118023/125000) 202 160
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t146 : ((75058973391/1000000000000 : ℚ) : ℝ) ≤ stT202 146 := by
  have hc : ((453471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75058973391/1000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((453471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c147 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-240369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 906771/2000000) (δ := 203/20000000) (ψ := 118023/125000) 202 160
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t147 : ((-198294465753/10000000000000 : ℚ) : ℝ) ≤ stT202 147 := by
  have hc : ((-240419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198294465753/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-240419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c148 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-999141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -193759/250000) (δ := 5073/500000000) (ψ := 118023/125000) 202 161
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t148 : ((-164266001209/2000000000000 : ℚ) : ℝ) ≤ stT202 148 := by
  have hc : ((-999191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164266001209/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-999191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c149 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-33651/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4349639/10000000) (δ := 10257/1000000000) (ψ := 118023/125000) 202 161
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t149 : ((-861755261/62500000000 : ℚ) : ℝ) ≤ stT202 149 := by
  have hc : ((-33661/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-861755261/62500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-33661/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c150 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((925403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -194349/2000000) (δ := 5073/500000000) (ψ := 118023/125000) 202 161
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t150 : ((47221688943/625000000000 : ℚ) : ℝ) ≤ stT202 150 := by
  have hc : ((925353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47221688943/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((925353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c151 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((578823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1191889/5000000) (δ := 5073/500000000) (ψ := 118023/125000) 202 161
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t151 : ((117749630531/2500000000000 : ℚ) : ℝ) ≤ stT202 151 := by
  have hc : ((578773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117749630531/2500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((578773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c152 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-131283/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1429283/2500000) (δ := 10257/1000000000) (ψ := 118023/125000) 202 161
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t152 : ((-26623200661/500000000000 : ℚ) : ℝ) ≤ stT202 152 := by
  have hc : ((-131293/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26623200661/500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-131293/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c153 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-445817/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1335869/2000000) (δ := 5119/500000000) (ψ := 118023/125000) 202 162
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t153 : ((-180221151213/2500000000000 : ℚ) : ℝ) ≤ stT202 153 := by
  have hc : ((-222921/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180221151213/2500000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-222921/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c154 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((1707/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3389421/10000000) (δ := 2033/200000000) (ψ := 118023/125000) 202 162
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t154 : ((3438039563/200000000000 : ℚ) : ℝ) ≤ stT202 154 := by
  have hc : ((8533/40000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3438039563/200000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((8533/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c155 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((998833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -120809/10000000) (δ := 5119/500000000) (ψ := 118023/125000) 202 162
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t155 : ((802241482477/10000000000000 : ℚ) : ℝ) ≤ stT202 155 := by
  have hc : ((998783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((802241482477/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((998783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c156 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((314641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 781699/2500000) (δ := 2033/200000000) (ψ := 118023/125000) 202 162
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t156 : ((393553341/15625000000 : ℚ) : ℝ) ≤ stT202 156 := by
  have hc : ((314591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((393553341/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((314591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c157 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-41263/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1270729/2000000) (δ := 2033/200000000) (ψ := 118023/125000) 202 162
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t157 : ((-65866918197/1000000000000 : ℚ) : ℝ) ≤ stT202 157 := by
  have hc : ((-82531/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65866918197/1000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-82531/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c158 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-776059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1536993/2500000) (δ := 321/31250000) (ψ := 118023/125000) 202 163
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t158 : ((-308719861911/5000000000000 : ℚ) : ℝ) ≤ stT202 158 := by
  have hc : ((-776109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-308719861911/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-776109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c159 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((376547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1480913/5000000) (δ := 321/31250000) (ψ := 118023/125000) 202 163
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t159 : ((298581322347/10000000000000 : ℚ) : ℝ) ≤ stT202 159 := by
  have hc : ((376497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298581322347/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((376497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c160 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((498331/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102161/5000000) (δ := 321/31250000) (ψ := 118023/125000) 202 163
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t160 : ((196972638057/2500000000000 : ℚ) : ℝ) ≤ stT202 160 := by
  have hc : ((249153/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196972638057/2500000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((249153/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c161 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((228471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 837681/2500000) (δ := 10131/1000000000) (ψ := 118023/125000) 202 163
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t161 : ((18002087431/1000000000000 : ℚ) : ℝ) ≤ stT202 161 := by
  have hc : ((228421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18002087431/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((228421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c162 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-852253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1619421/2500000) (δ := 10131/1000000000) (ψ := 118023/125000) 202 163
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t162 : ((-26785326381/400000000000 : ℚ) : ℝ) ≤ stT202 162 := by
  have hc : ((-852303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26785326381/400000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-852303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c163 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-96201/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19133/31250) (δ := 639/62500000) (ψ := 118023/125000) 202 164
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t163 : ((-301421547369/5000000000000 : ℚ) : ℝ) ≤ stT202 163 := by
  have hc : ((-384829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-301421547369/5000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-384829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c164 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((174847/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3033879/10000000) (δ := 639/62500000) (ψ := 118023/125000) 202 164
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t164 : ((17064113187/625000000000 : ℚ) : ℝ) ≤ stT202 164 := by
  have hc : ((87411/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17064113187/625000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((87411/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c165 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((124987/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2251/625000) (δ := 639/62500000) (ψ := 118023/125000) 202 164
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t165 : ((194594527827/2500000000000 : ℚ) : ℝ) ≤ stT202 165 := by
  have hc : ((499923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194594527827/2500000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((499923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c166 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((329567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1543689/5000000) (δ := 10179/1000000000) (ψ := 118023/125000) 202 164
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t166 : ((5115092391/200000000000 : ℚ) : ℝ) ≤ stT202 166 := by
  have hc : ((329517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5115092391/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((329517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c167 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-769071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3060229/5000000) (δ := 639/62500000) (ψ := 118023/125000) 202 164
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t167 : ((-9299442011/156250000000 : ℚ) : ℝ) ≤ stT202 167 := by
  have hc : ((-769121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9299442011/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-769121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c168 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-108937/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1643151/2500000) (δ := 5143/500000000) (ψ := 118023/125000) 202 165
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t168 : ((-336206277641/5000000000000 : ℚ) : ℝ) ≤ stT202 168 := by
  have hc : ((-435773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-336206277641/5000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-435773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c169 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((70061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -357553/1000000) (δ := 5143/500000000) (ψ := 118023/125000) 202 165
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t169 : ((1346844807/125000000000 : ℚ) : ℝ) ≤ stT202 169 := by
  have hc : ((17509/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1346844807/125000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((17509/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c170 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((9717/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -298091/5000000) (δ := 10117/1000000000) (ψ := 118023/125000) 202 165
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t170 : ((3726102853/50000000000 : ℚ) : ℝ) ≤ stT202 170 := by
  have hc : ((19433/20000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3726102853/50000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((19433/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c171 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((584707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1182847/5000000) (δ := 5143/500000000) (ψ := 118023/125000) 202 165
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t171 : ((447098316383/10000000000000 : ℚ) : ℝ) ≤ stT202 171 := by
  have hc : ((584657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((447098316383/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((584657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c172 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-525517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2655149/5000000) (δ := 10117/1000000000) (ψ := 118023/125000) 202 165
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t172 : ((-400741158531/10000000000000 : ℚ) : ℝ) ≤ stT202 172 := by
  have hc : ((-525567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-400741158531/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-525567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c173 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-247059/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -747013/1000000) (δ := 1021/100000000) (ψ := 118023/125000) 202 166
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t173 : ((-187845002449/2500000000000 : ℚ) : ℝ) ≤ stT202 173 := by
  have hc : ((-494143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187845002449/2500000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-494143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c174 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-125149/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4559461/10000000) (δ := 10193/1000000000) (ψ := 118023/125000) 202 166
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t174 : ((-47447142113/2500000000000 : ℚ) : ℝ) ≤ stT202 174 := by
  have hc : ((-62587/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47447142113/2500000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-62587/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c175 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((393093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -832729/5000000) (δ := 1021/100000000) (ψ := 118023/125000) 202 166
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t175 : ((9285347097/156250000000 : ℚ) : ℝ) ≤ stT202 175 := by
  have hc : ((98267/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9285347097/156250000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((98267/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c176 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((442381/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9469/78125) (δ := 1021/100000000) (ψ := 118023/125000) 202 166
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t176 : ((41679777621/625000000000 : ℚ) : ℝ) ≤ stT202 176 := by
  have hc : ((110589/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41679777621/625000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((110589/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c177 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-2339/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4073261/10000000) (δ := 1021/100000000) (ψ := 118023/125000) 202 166
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t177 : ((-1759605627/400000000000 : ℚ) : ℝ) ≤ stT202 177 := by
  have hc : ((-2341/40000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1759605627/400000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-2341/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c178 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-465389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 691833/1000000) (δ := 1021/100000000) (ψ := 118023/125000) 202 166
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t178 : ((-43605335781/625000000000 : ℚ) : ℝ) ≤ stT202 178 := by
  have hc : ((-232707/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43605335781/625000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-232707/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c179 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-363311/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5960471/10000000) (δ := 103/10000000) (ψ := 118023/125000) 202 167
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t179 : ((-8486575203/156250000000 : ℚ) : ℝ) ≤ stT202 179 := by
  have hc : ((-45417/62500 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8486575203/156250000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-45417/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c180 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((61383/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -786779/2500000) (δ := 103/10000000) (ψ := 118023/125000) 202 167
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t180 : ((9148934483/400000000000 : ℚ) : ℝ) ≤ stT202 180 := by
  have hc : ((61373/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9148934483/400000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((61373/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c181 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((495127/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -69863/2000000) (δ := 103/10000000) (ψ := 118023/125000) 202 167
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t181 : ((92001586497/1250000000000 : ℚ) : ℝ) ≤ stT202 181 := by
  have hc : ((247551/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92001586497/1250000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((247551/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c182 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((281323/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2433033/10000000) (δ := 103/10000000) (ψ := 118023/125000) 202 167
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t182 : ((104255930601/2500000000000 : ℚ) : ℝ) ≤ stT202 182 := by
  have hc : ((140649/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104255930601/2500000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((140649/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c183 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-97509/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 260009/500000) (δ := 10103/1000000000) (ψ := 118023/125000) 202 167
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t183 : ((-36044095109/1000000000000 : ℚ) : ℝ) ≤ stT202 183 := by
  have hc : ((-97519/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36044095109/1000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-97519/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c184 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-249807/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1551147/2000000) (δ := 319/31250000) (ψ := 118023/125000) 202 168
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t184 : ((-36833886719/500000000000 : ℚ) : ℝ) ≤ stT202 184 := by
  have hc : ((-499639/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36833886719/500000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-499639/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c185 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-84579/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1003717/2000000) (δ := 2039/200000000) (ψ := 118023/125000) 202 168
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t185 : ((-12438220327/400000000000 : ℚ) : ℝ) ≤ stT202 185 := by
  have hc : ((-84589/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12438220327/400000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-84589/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c186 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((607019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2296231/10000000) (δ := 2039/200000000) (ψ := 118023/125000) 202 168
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t186 : ((89010182943/2000000000000 : ℚ) : ℝ) ≤ stT202 186 := by
  have hc : ((606969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89010182943/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((606969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c187 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((986479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 411579/10000000) (δ := 2039/200000000) (ψ := 118023/125000) 202 168
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t187 : ((90168488461/1250000000000 : ℚ) : ℝ) ≤ stT202 187 := by
  have hc : ((986429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90168488461/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((986429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c188 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((322943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24257/78125) (δ := 319/31250000) (ψ := 118023/125000) 202 168
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t188 : ((58873403583/2500000000000 : ℚ) : ℝ) ≤ stT202 188 := by
  have hc : ((322893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58873403583/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((322893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c189 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-676347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5783971/10000000) (δ := 2039/200000000) (ψ := 118023/125000) 202 168
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t189 : ((-492006443021/10000000000000 : ℚ) : ℝ) ≤ stT202 189 := by
  have hc : ((-676397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-492006443021/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-676397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c190 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-971823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7259107/10000000) (δ := 2023/200000000) (ψ := 118023/125000) 202 169
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t190 : ((-705071508421/10000000000000 : ℚ) : ℝ) ≤ stT202 190 := by
  have hc : ((-971873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-705071508421/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-971873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c191 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-269109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28801/62500) (δ := 2023/200000000) (ψ := 118023/125000) 202 169
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t191 : ((-7790268937/400000000000 : ℚ) : ℝ) ≤ stT202 191 := by
  have hc : ((-269159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7790268937/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-269159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c192 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((88119/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1971101/10000000) (δ := 643/62500000) (ψ := 118023/125000) 202 169
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t192 : ((254359304837/5000000000000 : ℚ) : ℝ) ≤ stT202 192 := by
  have hc : ((352451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254359304837/5000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((352451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c193 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((241539/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 652273/10000000) (δ := 643/62500000) (ψ := 118023/125000) 202 169
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t193 : ((69541759039/1000000000000 : ℚ) : ℝ) ≤ stT202 193 := by
  have hc : ((483053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69541759039/1000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((483053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c194 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((262827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3262113/10000000) (δ := 643/62500000) (ψ := 118023/125000) 202 169
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t194 : ((94331424683/5000000000000 : ℚ) : ℝ) ≤ stT202 194 := by
  have hc : ((262777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94331424683/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((262777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c195 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-87251/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 146463/250000) (δ := 643/62500000) (ψ := 118023/125000) 202 169
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t195 : ((-49988980467/1000000000000 : ℚ) : ℝ) ≤ stT202 195 := by
  have hc : ((-349029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49988980467/1000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-349029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c196 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-972499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7266317/10000000) (δ := 5111/500000000) (ψ := 118023/125000) 202 170
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t196 : ((-347339067507/5000000000000 : ℚ) : ℝ) ≤ stT202 196 := by
  have hc : ((-972549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-347339067507/5000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-972549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c197 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-151449/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2348161/5000000) (δ := 10181/1000000000) (ψ := 118023/125000) 202 170
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t197 : ((-53960416127/2500000000000 : ℚ) : ℝ) ≤ stT202 197 := by
  have hc : ((-75737/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53960416127/2500000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-75737/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c198 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((327829/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -427871/2000000) (δ := 5111/500000000) (ψ := 118023/125000) 202 170
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t198 : ((58240035219/1250000000000 : ℚ) : ℝ) ≤ stT202 198 := by
  have hc : ((81951/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58240035219/1250000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((81951/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c199 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((246731/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 202367/5000000) (δ := 5111/500000000) (ψ := 118023/125000) 202 170
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t199 : ((349788113997/5000000000000 : ℚ) : ℝ) ≤ stT202 199 := by
  have hc : ((493437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((349788113997/5000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((493437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c200 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((2413/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1468023/5000000) (δ := 10181/1000000000) (ψ := 118023/125000) 202 170
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t200 : ((13648206459/500000000000 : ℚ) : ℝ) ≤ stT202 200 := by
  have hc : ((38603/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13648206459/500000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((38603/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c201 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-573783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 85231/156250) (δ := 10181/1000000000) (ψ := 118023/125000) 202 170
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t201 : ((-202375405609/5000000000000 : ℚ) : ℝ) ≤ stT202 201 := by
  have hc : ((-573833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202375405609/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-573833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c202 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-199817/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -968377/1250000) (δ := 5137/500000000) (ψ := 118023/125000) 202 171
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t202 : ((-70298938773/1000000000000 : ℚ) : ℝ) ≤ stT202 202 := by
  have hc : ((-199827/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70298938773/1000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-199827/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c203 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-252971/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2626587/5000000) (δ := 10129/1000000000) (ψ := 118023/125000) 202 171
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t203 : ((-44392132887/1250000000000 : ℚ) : ℝ) ≤ stT202 203 := by
  have hc : ((-63249/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44392132887/1250000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-63249/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c204 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((222939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -692901/2500000) (δ := 10129/1000000000) (ψ := 118023/125000) 202 171
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t204 : ((3901775199/125000000000 : ℚ) : ℝ) ≤ stT202 204 := by
  have hc : ((111457/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3901775199/125000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((111457/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c205 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((198541/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -151077/5000000) (δ := 10129/1000000000) (ψ := 118023/125000) 202 171
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t205 : ((13866000633/200000000000 : ℚ) : ℝ) ≤ stT202 205 := by
  have hc : ((198531/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13866000633/200000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((198531/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c206 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((162709/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2155277/10000000) (δ := 10129/1000000000) (ψ := 118023/125000) 202 171
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t206 : ((226712041069/5000000000000 : ℚ) : ℝ) ≤ stT202 206 := by
  have hc : ((325393/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226712041069/5000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((325393/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c207 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-66567/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 460079/1000000) (δ := 10129/1000000000) (ψ := 118023/125000) 202 171
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t207 : ((-92552029791/5000000000000 : ℚ) : ℝ) ≤ stT202 207 := by
  have hc : ((-133159/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92552029791/5000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-133159/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c208 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-23669/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 879317/1250000) (δ := 5137/500000000) (ψ := 118023/125000) 202 171
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t208 : ((-512886977/7812500000 : ℚ) : ℝ) ≤ stT202 208 := by
  have hc : ((-94681/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512886977/7812500000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-94681/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c209 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-400733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3125673/5000000) (δ := 10167/1000000000) (ψ := 118023/125000) 202 172
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t209 : ((-27721031997/500000000000 : ℚ) : ℝ) ≤ stT202 209 := by
  have hc : ((-200379/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27721031997/500000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-200379/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c210 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((17229/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3840829/10000000) (δ := 2559/250000000) (ψ := 118023/125000) 202 172
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t210 : ((593593913/250000000000 : ℚ) : ℝ) ≤ stT202 210 := by
  have hc : ((4301/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((593593913/250000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((4301/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c211 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((838261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -90111/625000) (δ := 2559/250000000) (ψ := 118023/125000) 202 172
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t211 : ((144261980577/2500000000000 : ℚ) : ℝ) ≤ stT202 211 := by
  have hc : ((838211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144261980577/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((838211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c212 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((92927/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 472957/5000000) (δ := 10167/1000000000) (ψ := 118023/125000) 202 172
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t212 : ((15954753861/250000000000 : ℚ) : ℝ) ≤ stT202 212 := by
  have hc : ((46461/50000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15954753861/250000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((46461/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c213 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((3742/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1661197/5000000) (δ := 2559/250000000) (ψ := 118023/125000) 202 172
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t213 : ((20507505543/1250000000000 : ℚ) : ℝ) ≤ stT202 213 := by
  have hc : ((119719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20507505543/1250000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((119719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c214 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-647507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5687763/10000000) (δ := 10167/1000000000) (ψ := 118023/125000) 202 172
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t214 : ((-221330449701/5000000000000 : ℚ) : ℝ) ≤ stT202 214 := by
  have hc : ((-647557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221330449701/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-647557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c215 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-997171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -766589/1000000) (δ := 317/31250000) (ψ := 118023/125000) 202 173
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t215 : ((-136019947179/2000000000000 : ℚ) : ℝ) ≤ stT202 215 := by
  have hc : ((-997221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136019947179/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-997221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c216 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-529659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -665311/1250000) (δ := 317/31250000) (ψ := 118023/125000) 202 173
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t216 : ((-180210709763/5000000000000 : ℚ) : ℝ) ≤ stT202 216 := by
  have hc : ((-529709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180210709763/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-529709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c217 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((45763/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -373743/1250000) (δ := 10259/1000000000) (ψ := 118023/125000) 202 173
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t217 : ((31061695197/1250000000000 : ℚ) : ℝ) ≤ stT202 217 := by
  have hc : ((183027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31061695197/1250000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((183027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c218 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((964503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -133621/2000000) (δ := 317/31250000) (ψ := 118023/125000) 202 173
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t218 : ((130641910021/2000000000000 : ℚ) : ℝ) ≤ stT202 218 := by
  have hc : ((964453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130641910021/2000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((964453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c219 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((31667/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 205391/1250000) (δ := 10259/1000000000) (ψ := 118023/125000) 202 173
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t219 : ((4279442421/80000000000 : ℚ) : ℝ) ≤ stT202 219 := by
  have hc : ((6333/8000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4279442421/80000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((6333/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c220 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-3363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3943807/10000000) (δ := 10259/1000000000) (ψ := 118023/125000) 202 173
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t220 : ((-2855237/6250000000 : ℚ) : ℝ) ≤ stT202 220 := by
  have hc : ((-847/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2855237/6250000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-847/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c221 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-797317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6234083/10000000) (δ := 10259/1000000000) (ψ := 118023/125000) 202 173
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t221 : ((-536367251991/10000000000000 : ℚ) : ℝ) ≤ stT202 221 := by
  have hc : ((-797367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-536367251991/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-797367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c222 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-965357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7194007/10000000) (δ := 1269/125000000) (ψ := 118023/125000) 202 174
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t222 : ((-647939665899/10000000000000 : ℚ) : ℝ) ≤ stT202 222 := by
  have hc : ((-965407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-647939665899/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-965407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c223 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-9711/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -984867/2000000) (δ := 1269/125000000) (ψ := 118023/125000) 202 174
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t223 : ((-520304657/20000000000 : ℚ) : ℝ) ≤ stT202 223 := by
  have hc : ((-38849/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-520304657/20000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-38849/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c224 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((96739/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2664813/10000000) (δ := 10251/1000000000) (ψ := 118023/125000) 202 174
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t224 : ((64629771537/2000000000000 : ℚ) : ℝ) ≤ stT202 224 := by
  have hc : ((96729/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64629771537/2000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((96729/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c225 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((986231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -415341/10000000) (δ := 10251/1000000000) (ψ := 118023/125000) 202 174
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t225 : ((328726671273/5000000000000 : ℚ) : ℝ) ≤ stT202 225 := by
  have hc : ((986181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((328726671273/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((986181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c226 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((745413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 912053/5000000) (δ := 159/7812500) (ψ := 118023/125000) 202 174
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t226 : ((49580801397/1000000000000 : ℚ) : ℝ) ≤ stT202 226 := by
  have hc : ((745363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49580801397/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((745363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c227 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-10133/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4053707/10000000) (δ := 10251/1000000000) (ψ := 118023/125000) 202 174
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t227 : ((-1683038133/500000000000 : ℚ) : ℝ) ≤ stT202 227 := by
  have hc : ((-10143/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1683038133/500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-10143/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c228 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-80673/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1254697/2000000) (δ := 10251/1000000000) (ψ := 118023/125000) 202 174
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t228 : ((-26715188513/500000000000 : ℚ) : ℝ) ≤ stT202 228 := by
  have hc : ((-40339/50000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26715188513/500000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-40339/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c229 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-968457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7224397/10000000) (δ := 2049/200000000) (ψ := 118023/125000) 202 175
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t229 : ((-640007827233/10000000000000 : ℚ) : ℝ) ≤ stT202 229 := by
  have hc : ((-968507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-640007827233/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-968507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c230 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-212421/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -125599/250000) (δ := 5079/500000000) (ψ := 118023/125000) 202 175
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t230 : ((-70041427963/2500000000000 : ℚ) : ℝ) ≤ stT202 230 := by
  have hc : ((-106223/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70041427963/2500000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-106223/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c231 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((423739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -708267/2500000) (δ := 5079/500000000) (ψ := 118023/125000) 202 175
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t231 : ((278766601239/10000000000000 : ℚ) : ℝ) ≤ stT202 231 := by
  have hc : ((423689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((278766601239/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((423689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c232 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((483109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65167/1000000) (δ := 5079/500000000) (ψ := 118023/125000) 202 175
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t232 : ((19822506543/312500000000 : ℚ) : ℝ) ≤ stT202 232 := by
  have hc : ((120771/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19822506543/312500000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((120771/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c233 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((25647/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 304077/2000000) (δ := 2049/200000000) (ψ := 118023/125000) 202 175
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t233 : ((268813834567/5000000000000 : ℚ) : ℝ) ≤ stT202 233 := by
  have hc : ((410327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268813834567/5000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((410327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c234 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((48691/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3683149/10000000) (δ := 5079/500000000) (ψ := 118023/125000) 202 175
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t234 : ((397674219/62500000000 : ℚ) : ℝ) ≤ stT202 234 := by
  have hc : ((24333/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((397674219/62500000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((24333/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c235 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-691723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5836671/10000000) (δ := 5079/500000000) (ψ := 118023/125000) 202 175
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t235 : ((-451263589317/10000000000000 : ℚ) : ℝ) ≤ stT202 235 := by
  have hc : ((-691773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-451263589317/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-691773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c236 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-998709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7726911/10000000) (δ := 5069/500000000) (ψ := 118023/125000) 202 176
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t236 : ((-130027435451/2000000000000 : ℚ) : ℝ) ≤ stT202 236 := by
  have hc : ((-998759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130027435451/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-998759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c237 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-617729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5591619/10000000) (δ := 2053/200000000) (ψ := 118023/125000) 202 176
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t237 : ((-40129070503/1000000000000 : ℚ) : ℝ) ≤ stT202 237 := by
  have hc : ((-617779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40129070503/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-617779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c238 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((91811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3465317/10000000) (δ := 5069/500000000) (ψ := 118023/125000) 202 176
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t238 : ((29747980279/2500000000000 : ℚ) : ℝ) ≤ stT202 238 := by
  have hc : ((45893/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29747980279/2500000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((45893/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c239 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((42907/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -673951/5000000) (δ := 2053/200000000) (ψ := 118023/125000) 202 176
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t239 : ((27752604207/500000000000 : ℚ) : ℝ) ≤ stT202 239 := by
  have hc : ((85809/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27752604207/500000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((85809/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c240 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((477033/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30427/400000) (δ := 2053/200000000) (ψ := 118023/125000) 202 176
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t240 : ((19244202061/312500000000 : ℚ) : ℝ) ≤ stT202 240 := by
  have hc : ((29813/31250 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19244202061/312500000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((29813/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c241 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((413787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 572093/2000000) (δ := 2053/200000000) (ψ := 118023/125000) 202 176
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t241 : ((66627792743/2500000000000 : ℚ) : ℝ) ≤ stT202 241 := by
  have hc : ((413737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66627792743/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((413737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c242 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-79691/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4951569/10000000) (δ := 2053/200000000) (ψ := 118023/125000) 202 176
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t242 : ((-2049351813/80000000000 : ℚ) : ℝ) ≤ stT202 242 := by
  have hc : ((-79701/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2049351813/80000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-79701/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c243 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-118337/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7034037/10000000) (δ := 5069/500000000) (ψ := 118023/125000) 202 176
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t243 : ((-303669252873/5000000000000 : ℚ) : ℝ) ≤ stT202 243 := by
  have hc : ((-473373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-303669252873/5000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-473373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c244 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-54801/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -824999/1250000) (δ := 2543/250000000) (ψ := 118023/125000) 202 177
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t244 : ((-56135646021/1000000000000 : ℚ) : ℝ) ≤ stT202 244 := by
  have hc : ((-438433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56135646021/1000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-438433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c245 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-48129/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4534567/10000000) (δ := 5093/250000000) (ψ := 118023/125000) 202 177
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t245 : ((-30754899903/2000000000000 : ℚ) : ℝ) ≤ stT202 245 := by
  have hc : ((-48139/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30754899903/2000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-48139/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c246 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((109569/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1238763/5000000) (δ := 10231/1000000000) (ψ := 118023/125000) 202 177
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t246 : ((8731523623/250000000000 : ℚ) : ℝ) ≤ stT202 246 := by
  have hc : ((109559/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8731523623/250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((109559/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c247 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((246331/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -214421/5000000) (δ := 10231/1000000000) (ψ := 118023/125000) 202 177
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t247 : ((78364260227/1250000000000 : ℚ) : ℝ) ≤ stT202 247 := by
  have hc : ((492637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78364260227/1250000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((492637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c248 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((399663/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40289/250000) (δ := 10231/1000000000) (ψ := 118023/125000) 202 177
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t248 : ((25377013/500000000 : ℚ) : ℝ) ≤ stT202 248 := by
  have hc : ((199819/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25377013/500000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((199819/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c249 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((56531/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3643731/10000000) (δ := 2543/250000000) (ψ := 118023/125000) 202 177
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t249 : ((4476151043/625000000000 : ℚ) : ℝ) ≤ stT202 249 := by
  have hc : ((28253/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4476151043/625000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((28253/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c250 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-10022/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5667821/10000000) (δ := 10231/1000000000) (ψ := 118023/125000) 202 177
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t250 : ((-25355872553/625000000000 : ℚ) : ℝ) ≤ stT202 250 := by
  have hc : ((-320729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25355872553/625000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-320729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c251 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-997683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7683781/10000000) (δ := 10231/1000000000) (ψ := 118023/125000) 202 177
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t251 : ((-125952816187/2000000000000 : ℚ) : ℝ) ≤ stT202 251 := by
  have hc : ((-997733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).2
  have h0 : (0:ℝ) ≤ ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125952816187/2000000000000 : ℚ) : ℝ)
      = ((126239/2000000 : ℚ) : ℝ) * ((-997733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c252 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-741769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6016251/10000000) (δ := 10279/1000000000) (ψ := 118023/125000) 202 178
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t252 : ((-467302202679/10000000000000 : ℚ) : ℝ) ≤ stT202 252 := by
  have hc : ((-741819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).2
  have h0 : (0:ℝ) ≤ ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-467302202679/10000000000000 : ℚ) : ℝ)
      = ((629941/10000000 : ℚ) : ℝ) * ((-741819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c253 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-2231/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4016249/10000000) (δ := 10279/1000000000) (ψ := 118023/125000) 202 178
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t253 : ((-2247333147/1000000000000 : ℚ) : ℝ) ≤ stT202 253 := by
  have hc : ((-17873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2247333147/1000000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-17873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c254 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((86219/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16193/80000) (δ := 10279/1000000000) (ψ := 118023/125000) 202 178
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t254 : ((43275696841/1000000000000 : ℚ) : ℝ) ≤ stT202 254 := by
  have hc : ((344851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).1
  have hw2 : ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((125491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43275696841/1000000000000 : ℚ) : ℝ)
      = ((125491/2000000 : ℚ) : ℝ) * ((344851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c255 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((999873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -39829/10000000) (δ := 2531/250000000) (ψ := 118023/125000) 202 178
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t255 : ((39132072397/625000000000 : ℚ) : ℝ) ≤ stT202 255 := by
  have hc : ((999823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).1
  have hw2 : ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39139/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39132072397/625000000000 : ℚ) : ℝ)
      = ((39139/625000 : ℚ) : ℝ) * ((999823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c256 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((714647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1936691/10000000) (δ := 10279/1000000000) (ψ := 118023/125000) 202 178
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t256 : ((714597/16000000 : ℚ) : ℝ) ≤ stT202 256 := by
  have hc : ((714597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).1
  have hw2 : ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((714597/16000000 : ℚ) : ℝ)
      = ((1/16 : ℚ) : ℝ) * ((714597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c257 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((8603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 976371/2500000) (δ := 10279/1000000000) (ψ := 118023/125000) 202 178
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t257 : ((2667603723/5000000000000 : ℚ) : ℝ) ≤ stT202 257 := by
  have hc : ((8553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2667603723/5000000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((8553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c258 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-700333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5866651/10000000) (δ := 2531/250000000) (ψ := 118023/125000) 202 178
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t258 : ((-436039545459/10000000000000 : ℚ) : ℝ) ≤ stT202 258 := by
  have hc : ((-700383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).2
  have h0 : (0:ℝ) ≤ ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-436039545459/10000000000000 : ℚ) : ℝ)
      = ((622573/10000000 : ℚ) : ℝ) * ((-700383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c259 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-999909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1955061/2500000) (δ := 10279/1000000000) (ψ := 118023/125000) 202 178
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t259 : ((-62134452383/1000000000000 : ℚ) : ℝ) ≤ stT202 259 := by
  have hc : ((-999959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).2
  have h0 : (0:ℝ) ≤ ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62134452383/1000000000000 : ℚ) : ℝ)
      = ((62137/1000000 : ℚ) : ℝ) * ((-999959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c260 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-72143/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1485413/2500000) (δ := 1277/125000000) (ψ := 118023/125000) 202 179
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t260 : ((-5593039219/125000000000 : ℚ) : ℝ) ≤ stT202 260 := by
  have hc : ((-18037/25000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5593039219/125000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-18037/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c261 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-15211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2001529/5000000) (δ := 1277/125000000) (ψ := 118023/125000) 202 179
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t261 : ((-471542773/250000000000 : ℚ) : ℝ) ≤ stT202 261 := by
  have hc : ((-3809/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-471542773/250000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-3809/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c262 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((337897/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2071887/10000000) (δ := 30387/1000000000) (ψ := 118023/125000) 202 179
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t262 : ((6523062417/156250000000 : ℚ) : ℝ) ≤ stT202 262 := by
  have hc : ((21117/31250 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).1
  have hw2 : ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6523062417/156250000000 : ℚ) : ℝ)
      = ((308901/5000000 : ℚ) : ℝ) * ((21117/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c263 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((499123/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14809/1000000) (δ := 1277/125000000) (ψ := 118023/125000) 202 179
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t263 : ((76939200837/1250000000000 : ℚ) : ℝ) ≤ stT202 263 := by
  have hc : ((249549/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76939200837/1250000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((249549/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c264 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((760071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 442109/2500000) (δ := 30387/1000000000) (ψ := 118023/125000) 202 179
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t264 : ((467760244597/10000000000000 : ℚ) : ℝ) ≤ stT202 264 := by
  have hc : ((760021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((467760244597/10000000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((760021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c265 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((24889/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3677689/10000000) (δ := 1277/125000000) (ψ := 118023/125000) 202 179
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t265 : ((6112603827/1000000000000 : ℚ) : ℝ) ≤ stT202 265 := by
  have hc : ((49753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6112603827/1000000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((49753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c266 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-122799/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1394943/2500000) (δ := 10187/1000000000) (ψ := 118023/125000) 202 179
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t266 : ((-3764955513/100000000000 : ℚ) : ℝ) ≤ stT202 266 := by
  have hc : ((-122809/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3764955513/100000000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-122809/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c267 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-988513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7474683/10000000) (δ := 1277/125000000) (ψ := 118023/125000) 202 179
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t267 : ((-604991658933/10000000000000 : ℚ) : ℝ) ≤ stT202 267 := by
  have hc : ((-988563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-604991658933/10000000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-988563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c268 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-823401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3172719/5000000) (δ := 5147/500000000) (ψ := 118023/125000) 202 180
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t268 : ((-15718856139/312500000000 : ℚ) : ℝ) ≤ stT202 268 := by
  have hc : ((-823451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15718856139/312500000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-823451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c269 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-53349/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -558077/1250000) (δ := 5147/500000000) (ψ := 118023/125000) 202 180
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t269 : ((-65070187053/5000000000000 : ℚ) : ℝ) ≤ stT202 269 := by
  have hc : ((-106723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).2
  have h0 : (0:ℝ) ≤ ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65070187053/5000000000000 : ℚ) : ℝ)
      = ((609711/10000000 : ℚ) : ℝ) * ((-106723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c270 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((509403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2590763/10000000) (δ := 5147/500000000) (ψ := 118023/125000) 202 180
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t270 : ((15499102437/500000000000 : ℚ) : ℝ) ≤ stT202 270 := by
  have hc : ((509353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15499102437/500000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((509353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c271 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((479189/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -723829/10000000) (δ := 10109/1000000000) (ψ := 118023/125000) 202 180
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t271 : ((2273992553/39062500000 : ℚ) : ℝ) ≤ stT202 271 := by
  have hc : ((119791/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2273992553/39062500000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((119791/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c272 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((224623/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1136187/10000000) (δ := 10109/1000000000) (ψ := 118023/125000) 202 180
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t272 : ((272380211919/5000000000000 : ℚ) : ℝ) ≤ stT202 272 := by
  have hc : ((449221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).1
  have hw2 : ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272380211919/5000000000000 : ℚ) : ℝ)
      = ((606339/10000000 : ℚ) : ℝ) * ((449221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c273 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((45789/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1494693/5000000) (δ := 5147/500000000) (ψ := 118023/125000) 202 180
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t273 : ((110835825737/5000000000000 : ℚ) : ℝ) ≤ stT202 273 := by
  have hc : ((183131/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).1
  have hw2 : ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((605227/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110835825737/5000000000000 : ℚ) : ℝ)
      = ((605227/10000000 : ℚ) : ℝ) * ((183131/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c274 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-71119/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1208967/2500000) (δ := 5147/500000000) (ψ := 118023/125000) 202 180
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t274 : ((-42970664867/2000000000000 : ℚ) : ℝ) ≤ stT202 274 := by
  have hc : ((-71129/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42970664867/2000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-71129/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c275 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-890943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1668883/2500000) (δ := 10109/1000000000) (ψ := 118023/125000) 202 180
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t275 : ((-537289271839/10000000000000 : ℚ) : ℝ) ≤ stT202 275 := by
  have hc : ((-890993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-537289271839/10000000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-890993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c276 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-193183/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3599691/5000000) (δ := 10201/1000000000) (ψ := 118023/125000) 202 181
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t276 : ((-11628866249/200000000000 : ℚ) : ℝ) ≤ stT202 276 := by
  have hc : ((-193193/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).2
  have h0 : (0:ℝ) ≤ ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11628866249/200000000000 : ℚ) : ℝ)
      = ((60193/1000000 : ℚ) : ℝ) * ((-193193/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c277 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-546671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5372949/10000000) (δ := 5101/500000000) (ψ := 118023/125000) 202 181
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t277 : ((-164246469541/5000000000000 : ℚ) : ℝ) ≤ stT202 277 := by
  have hc : ((-546721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).2
  have h0 : (0:ℝ) ≤ ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164246469541/5000000000000 : ℚ) : ℝ)
      = ((300421/5000000 : ℚ) : ℝ) * ((-546721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c278 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((148987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3553131/10000000) (δ := 5101/500000000) (ψ := 118023/125000) 202 181
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t278 : ((1116580689/125000000000 : ℚ) : ℝ) ≤ stT202 278 := by
  have hc : ((148937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1116580689/125000000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((148937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c279 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((191861/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -869939/5000000) (δ := 5101/500000000) (ψ := 118023/125000) 202 181
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t279 : ((57428313687/1250000000000 : ℚ) : ℝ) ≤ stT202 279 := by
  have hc : ((383697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).1
  have hw2 : ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149671/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57428313687/1250000000000 : ℚ) : ℝ)
      = ((149671/2500000 : ℚ) : ℝ) * ((383697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c280 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((999641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33481/5000000) (δ := 10201/1000000000) (ψ := 118023/125000) 202 181
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t280 : ((298684787937/5000000000000 : ℚ) : ℝ) ≤ stT202 280 := by
  have hc : ((999591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).1
  have hw2 : ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298684787937/5000000000000 : ℚ) : ℝ)
      = ((298807/5000000 : ℚ) : ℝ) * ((999591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c281 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((183447/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1867287/10000000) (δ := 10201/1000000000) (ψ := 118023/125000) 202 181
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t281 : ((218855335081/5000000000000 : ℚ) : ℝ) ≤ stT202 281 := by
  have hc : ((366869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).1
  have hw2 : ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((596549/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218855335081/5000000000000 : ℚ) : ℝ)
      = ((596549/10000000 : ℚ) : ℝ) * ((366869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c282 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((106097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3661249/10000000) (δ := 10201/1000000000) (ψ := 118023/125000) 202 181
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t282 : ((63150034077/10000000000000 : ℚ) : ℝ) ≤ stT202 282 := by
  have hc : ((106047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63150034077/10000000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((106047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c283 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-571837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 340553/625000) (δ := 10201/1000000000) (ψ := 118023/125000) 202 181
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t283 : ((-339951936393/10000000000000 : ℚ) : ℝ) ≤ stT202 283 := by
  have hc : ((-571887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).2
  have h0 : (0:ℝ) ≤ ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-339951936393/10000000000000 : ℚ) : ℝ)
      = ((594439/10000000 : ℚ) : ℝ) * ((-571887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c284 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-969031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1446037/2000000) (δ := 10201/1000000000) (ψ := 118023/125000) 202 181
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t284 : ((-575043943671/10000000000000 : ℚ) : ℝ) ≤ stT202 284 := by
  have hc : ((-969081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).2
  have h0 : (0:ℝ) ≤ ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-575043943671/10000000000000 : ℚ) : ℝ)
      = ((593391/10000000 : ℚ) : ℝ) * ((-969081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c285 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-447917/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3351377/5000000) (δ := 2527/250000000) (ψ := 118023/125000) 202 182
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t285 : ((-132668997879/2500000000000 : ℚ) : ℝ) ≤ stT202 285 := by
  have hc : ((-223971/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132668997879/2500000000000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-223971/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c286 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-391959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4933891/10000000) (δ := 2059/200000000) (ψ := 118023/125000) 202 182
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t286 : ((-231800017817/10000000000000 : ℚ) : ℝ) ≤ stT202 286 := by
  have hc : ((-392009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-231800017817/10000000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-392009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c287 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((297717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3171239/10000000) (δ := 2059/200000000) (ψ := 118023/125000) 202 182
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t287 : ((175707174427/10000000000000 : ℚ) : ℝ) ≤ stT202 287 := by
  have hc : ((297667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).1
  have hw2 : ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((590281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175707174427/10000000000000 : ℚ) : ℝ)
      = ((590281/10000000 : ℚ) : ℝ) * ((297667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c288 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((844107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -353687/2500000) (δ := 2059/200000000) (ψ := 118023/125000) 202 182
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t288 : ((99472961507/2000000000000 : ℚ) : ℝ) ≤ stT202 288 := by
  have hc : ((844057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99472961507/2000000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((844057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c289 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((990999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 335683/10000000) (δ := 2059/200000000) (ψ := 118023/125000) 202 182
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t289 : ((116582177003/2000000000000 : ℚ) : ℝ) ≤ stT202 289 := by
  have hc : ((990949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116582177003/2000000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((990949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c290 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((673367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 416021/2000000) (δ := 2527/250000000) (ψ := 118023/125000) 202 182
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t290 : ((19769260437/500000000000 : ℚ) : ℝ) ≤ stT202 290 := by
  have hc : ((673317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19769260437/500000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((673317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c291 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((10849/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1909233/5000000) (δ := 2059/200000000) (ψ := 118023/125000) 202 182
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t291 : ((1270492933/500000000000 : ℚ) : ℝ) ≤ stT202 291 := by
  have hc : ((21673/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1270492933/500000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((21673/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c292 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-120969/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5550919/10000000) (δ := 2059/200000000) (ψ := 118023/125000) 202 182
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t292 : ((-35398818337/1000000000000 : ℚ) : ℝ) ≤ stT202 292 := by
  have hc : ((-120979/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).2
  have h0 : (0:ℝ) ≤ ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35398818337/1000000000000 : ℚ) : ℝ)
      = ((292603/5000000 : ℚ) : ℝ) * ((-120979/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c293 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-973523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7277413/10000000) (δ := 2059/200000000) (ψ := 118023/125000) 202 182
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t293 : ((-568768161611/10000000000000 : ℚ) : ℝ) ≤ stT202 293 := by
  have hc : ((-973573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).2
  have h0 : (0:ℝ) ≤ ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-568768161611/10000000000000 : ℚ) : ℝ)
      = ((584207/10000000 : ℚ) : ℝ) * ((-973573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c294 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-112139/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1677491/2500000) (δ := 2043/200000000) (ψ := 118023/125000) 202 183
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t294 : ((-65404455543/1250000000000 : ℚ) : ℝ) ≤ stT202 294 := by
  have hc : ((-448581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65404455543/1250000000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-448581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c295 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-82879/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2497593/5000000) (δ := 2043/200000000) (ψ := 118023/125000) 202 183
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t295 : ((-48259882247/2000000000000 : ℚ) : ℝ) ≤ stT202 295 := by
  have hc : ((-82889/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).2
  have h0 : (0:ℝ) ≤ ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48259882247/2000000000000 : ℚ) : ℝ)
      = ((582223/10000000 : ℚ) : ℝ) * ((-82889/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c296 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((253513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -410777/1250000) (δ := 2547/250000000) (ψ := 118023/125000) 202 183
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t296 : ((73661163597/5000000000000 : ℚ) : ℝ) ≤ stT202 296 := by
  have hc : ((253463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).1
  have hw2 : ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73661163597/5000000000000 : ℚ) : ℝ)
      = ((290619/5000000 : ℚ) : ℝ) * ((253463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c297 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((403069/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -791501/5000000) (δ := 2043/200000000) (ψ := 118023/125000) 202 183
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t297 : ((29233688169/625000000000 : ℚ) : ℝ) ≤ stT202 297 := by
  have hc : ((100761/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).1
  have hw2 : ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290129/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29233688169/625000000000 : ℚ) : ℝ)
      = ((290129/5000000 : ℚ) : ℝ) * ((100761/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c298 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((124869/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57227/5000000) (δ := 2547/250000000) (ψ := 118023/125000) 202 183
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t298 : ((72330993271/1250000000000 : ℚ) : ℝ) ≤ stT202 298 := by
  have hc : ((499451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72330993271/1250000000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((499451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c299 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((375077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 361251/2000000) (δ := 2043/200000000) (ψ := 118023/125000) 202 183
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t299 : ((27112227791/625000000000 : ℚ) : ℝ) ≤ stT202 299 := by
  have hc : ((93763/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).1
  have hw2 : ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((289157/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27112227791/625000000000 : ℚ) : ℝ)
      = ((289157/5000000 : ℚ) : ℝ) * ((93763/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c300 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((172963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3492399/10000000) (δ := 2547/250000000) (ψ := 118023/125000) 202 183
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t300 : ((1996626411/200000000000 : ℚ) : ℝ) ≤ stT202 300 := by
  have hc : ((172913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1996626411/200000000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((172913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c301 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-239001/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2586469/5000000) (δ := 2547/250000000) (ψ := 118023/125000) 202 183
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t301 : ((-68886217583/2500000000000 : ℚ) : ℝ) ≤ stT202 301 := by
  have hc : ((-119513/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).2
  have h0 : (0:ℝ) ≤ ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68886217583/2500000000000 : ℚ) : ℝ)
      = ((576391/10000000 : ℚ) : ℝ) * ((-119513/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c302 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-460057/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3423961/5000000) (δ := 2547/250000000) (ψ := 118023/125000) 202 183
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t302 : ((-33093468219/625000000000 : ℚ) : ℝ) ≤ stT202 302 := by
  have hc : ((-230041/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33093468219/625000000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-230041/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c303 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-965001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1797653/2500000) (δ := 10123/1000000000) (ψ := 118023/125000) 202 184
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t303 : ((-110881464747/2000000000000 : ℚ) : ℝ) ≤ stT202 303 := by
  have hc : ((-965051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110881464747/2000000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-965051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c304 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-298549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -172709/312500) (δ := 257/25000000) (ψ := 118023/125000) 202 184
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t304 : ((-4281103299/125000000000 : ℚ) : ℝ) ≤ stT202 304 := by
  have hc : ((-149287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4281103299/125000000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-149287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c305 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((23487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -967067/2500000) (δ := 257/25000000) (ψ := 118023/125000) 202 184
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t305 : ((6709989663/5000000000000 : ℚ) : ℝ) ≤ stT202 305 := by
  have hc : ((23437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).1
  have hw2 : ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((286299/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6709989663/5000000000000 : ℚ) : ℝ)
      = ((286299/5000000 : ℚ) : ℝ) * ((23437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c306 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((632453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2215201/10000000) (δ := 257/25000000) (ψ := 118023/125000) 202 184
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t306 : ((361520131383/10000000000000 : ℚ) : ℝ) ≤ stT202 306 := by
  have hc : ((632403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).1
  have hw2 : ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((571661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((361520131383/10000000000000 : ℚ) : ℝ)
      = ((571661/10000000 : ℚ) : ℝ) * ((632403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c307 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((487169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -141897/2500000) (δ := 257/25000000) (ψ := 118023/125000) 202 184
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t307 : ((3475346189/62500000000 : ℚ) : ℝ) ≤ stT202 307 := by
  have hc : ((60893/62500 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3475346189/62500000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((60893/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c308 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((45451/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 67167/625000) (δ := 257/25000000) (ψ := 118023/125000) 202 184
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t308 : ((25896646197/500000000000 : ℚ) : ℝ) ≤ stT202 308 := by
  have hc : ((90897/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25896646197/500000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((90897/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c309 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((23361/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 271163/1000000) (δ := 10123/1000000000) (ψ := 118023/125000) 202 184
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t309 : ((332204587/12500000000 : ℚ) : ℝ) ≤ stT202 309 := by
  have hc : ((46717/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((332204587/12500000000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((46717/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c310 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-165749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 868657/2000000) (δ := 10123/1000000000) (ψ := 118023/125000) 202 184
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t310 : ((-47083765819/5000000000000 : ℚ) : ℝ) ≤ stT202 310 := by
  have hc : ((-165799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47083765819/5000000000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-165799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c311 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-182291/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2984869/5000000) (δ := 257/25000000) (ψ := 118023/125000) 202 184
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t311 : ((-25843708767/625000000000 : ℚ) : ℝ) ≤ stT202 311 := by
  have hc : ((-364607/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25843708767/625000000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-364607/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c312 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-248617/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7590889/10000000) (δ := 257/25000000) (ψ := 118023/125000) 202 184
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t312 : ((-281517713001/5000000000000 : ℚ) : ℝ) ≤ stT202 312 := by
  have hc : ((-497259/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-281517713001/5000000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-497259/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c313 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-85711/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3250537/5000000) (δ := 10173/1000000000) (ψ := 118023/125000) 202 185
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t313 : ((-6056199693/125000000000 : ℚ) : ℝ) ≤ stT202 313 := by
  have hc : ((-21429/25000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6056199693/125000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-21429/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c314 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-375831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -195609/400000) (δ := 10173/1000000000) (ψ := 118023/125000) 202 185
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t314 : ((-212122052373/10000000000000 : ℚ) : ℝ) ≤ stT202 314 := by
  have hc : ((-375881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).2
  have h0 : (0:ℝ) ≤ ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-212122052373/10000000000000 : ℚ) : ℝ)
      = ((564333/10000000 : ℚ) : ℝ) * ((-375881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c315 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((127093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -821119/2500000) (δ := 1023/100000000) (ψ := 118023/125000) 202 185
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t315 : ((4474667853/312500000000 : ℚ) : ℝ) ≤ stT202 315 := by
  have hc : ((31767/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4474667853/312500000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((31767/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c316 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((97703/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -420957/2500000) (δ := 1023/100000000) (ψ := 118023/125000) 202 185
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t316 : ((219834491341/5000000000000 : ℚ) : ℝ) ≤ stT202 316 := by
  have hc : ((390787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219834491341/5000000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((390787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c317 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((999377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -88281/10000000) (δ := 10173/1000000000) (ψ := 118023/125000) 202 185
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t317 : ((112255401237/2000000000000 : ℚ) : ℝ) ≤ stT202 317 := by
  have hc : ((999327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).1
  have hw2 : ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((112331/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112255401237/2000000000000 : ℚ) : ℝ)
      = ((112331/2000000 : ℚ) : ℝ) * ((999327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c318 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((824823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1502267/10000000) (δ := 10173/1000000000) (ψ := 118023/125000) 202 185
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t318 : ((115627401189/2500000000000 : ℚ) : ℝ) ≤ stT202 318 := by
  have hc : ((824773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).1
  have hw2 : ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140193/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115627401189/2500000000000 : ℚ) : ℝ)
      = ((140193/2500000 : ℚ) : ℝ) * ((824773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c319 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((329383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1543933/5000000) (δ := 10173/1000000000) (ψ := 118023/125000) 202 185
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t319 : ((46097728009/2500000000000 : ℚ) : ℝ) ≤ stT202 319 := by
  have hc : ((329333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).1
  have hw2 : ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((139973/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46097728009/2500000000000 : ℚ) : ℝ)
      = ((139973/2500000 : ℚ) : ℝ) * ((329333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c320 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-292241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 933683/2000000) (δ := 10173/1000000000) (ψ := 118023/125000) 202 185
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t320 : ((-163395637947/10000000000000 : ℚ) : ℝ) ≤ stT202 320 := by
  have hc : ((-292291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163395637947/10000000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-292291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c321 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-799733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1561029/2500000) (δ := 10173/1000000000) (ψ := 118023/125000) 202 185
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t321 : ((-223197841159/5000000000000 : ℚ) : ℝ) ≤ stT202 321 := by
  have hc : ((-799783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223197841159/5000000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-799783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c322 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-499939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1953717/2500000) (δ := 10173/1000000000) (ψ := 118023/125000) 202 185
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t322 : ((-69654859489/1250000000000 : ℚ) : ℝ) ≤ stT202 322 := by
  have hc : ((-124991/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).2
  have h0 : (0:ℝ) ≤ ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69654859489/1250000000000 : ℚ) : ℝ)
      = ((557279/10000000 : ℚ) : ℝ) * ((-124991/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c323 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-819237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6327191/10000000) (δ := 10137/1000000000) (ψ := 118023/125000) 202 186
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t323 : ((-91172715221/2000000000000 : ℚ) : ℝ) ≤ stT202 323 := by
  have hc : ((-819287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).2
  have h0 : (0:ℝ) ≤ ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91172715221/2000000000000 : ℚ) : ℝ)
      = ((111283/2000000 : ℚ) : ℝ) * ((-819287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c324 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-32939/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -953227/2000000) (δ := 10137/1000000000) (ψ := 118023/125000) 202 186
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t324 : ((-285972451/15625000000 : ℚ) : ℝ) ≤ stT202 324 := by
  have hc : ((-2059/6250 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).2
  have h0 : (0:ℝ) ≤ ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285972451/15625000000 : ℚ) : ℝ)
      = ((138889/2500000 : ℚ) : ℝ) * ((-2059/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c325 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((282909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3209927/10000000) (δ := 10137/1000000000) (ψ := 118023/125000) 202 186
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t325 : ((1569018873/100000000000 : ℚ) : ℝ) ≤ stT202 325 := by
  have hc : ((282859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1569018873/100000000000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((282859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c326 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((787911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -829233/5000000) (δ := 10137/1000000000) (ψ := 118023/125000) 202 186
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t326 : ((54544404891/1250000000000 : ℚ) : ℝ) ≤ stT202 326 := by
  have hc : ((787861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).1
  have hw2 : ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69231/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54544404891/1250000000000 : ℚ) : ℝ)
      = ((69231/1250000 : ℚ) : ℝ) * ((787861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c327 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((999001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13969/1250000) (δ := 10137/1000000000) (ψ := 118023/125000) 202 186
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t327 : ((552420901951/10000000000000 : ℚ) : ℝ) ≤ stT202 327 := by
  have hc : ((998951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).1
  have hw2 : ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((553001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((552420901951/10000000000000 : ℚ) : ℝ)
      = ((553001/10000000 : ℚ) : ℝ) * ((998951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c328 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((840763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 286053/2000000) (δ := 5133/500000000) (ψ := 118023/125000) 202 186
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t328 : ((464205567941/10000000000000 : ℚ) : ℝ) ≤ stT202 328 := by
  have hc : ((840713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).1
  have hw2 : ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((552157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((464205567941/10000000000000 : ℚ) : ℝ)
      = ((552157/10000000 : ℚ) : ℝ) * ((840713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c329 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((37443/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 185471/625000) (δ := 10137/1000000000) (ψ := 118023/125000) 202 186
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t329 : ((10320102923/500000000000 : ℚ) : ℝ) ≤ stT202 329 := by
  have hc : ((18719/50000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).1
  have hw2 : ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((551317/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10320102923/500000000000 : ℚ) : ℝ)
      = ((551317/10000000 : ℚ) : ℝ) * ((18719/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c330 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-3551/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14063/31250) (δ := 5133/500000000) (ψ := 118023/125000) 202 186
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t330 : ((-31283066337/2500000000000 : ℚ) : ℝ) ≤ stT202 330 := by
  have hc : ((-113657/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).2
  have h0 : (0:ℝ) ≤ ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31283066337/2500000000000 : ℚ) : ℝ)
      = ((275241/5000000 : ℚ) : ℝ) * ((-113657/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c331 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-14899/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6028139/10000000) (δ := 10137/1000000000) (ψ := 118023/125000) 202 186
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t331 : ((-1637957/40000000 : ℚ) : ℝ) ≤ stT202 331 := by
  have hc : ((-149/200 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1637957/40000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-149/200 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c332 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-99269/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3775761/5000000) (δ := 10137/1000000000) (ψ := 118023/125000) 202 186
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t332 : ((-13620938807/250000000000 : ℚ) : ℝ) ≤ stT202 332 := by
  have hc : ((-49637/50000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).2
  have h0 : (0:ℝ) ≤ ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13620938807/250000000000 : ℚ) : ℝ)
      = ((274411/5000000 : ℚ) : ℝ) * ((-49637/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c333 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-22099/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3318827/5000000) (δ := 10159/1000000000) (ψ := 118023/125000) 202 187
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t333 : ((-48443482797/1000000000000 : ℚ) : ℝ) ≤ stT202 333 := by
  have hc : ((-88401/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).2
  have h0 : (0:ℝ) ≤ ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48443482797/1000000000000 : ℚ) : ℝ)
      = ((547997/10000000 : ℚ) : ℝ) * ((-88401/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c334 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-460509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5123411/10000000) (δ := 2561/250000000) (ψ := 118023/125000) 202 187
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t334 : ((-31500853923/1250000000000 : ℚ) : ℝ) ≤ stT202 334 := by
  have hc : ((-460559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).2
  have h0 : (0:ℝ) ≤ ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31500853923/1250000000000 : ℚ) : ℝ)
      = ((68397/1250000 : ℚ) : ℝ) * ((-460559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c335 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((125003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3613663/10000000) (δ := 2561/250000000) (ψ := 118023/125000) 202 187
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t335 : ((34134535587/5000000000000 : ℚ) : ℝ) ≤ stT202 335 := by
  have hc : ((124953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34134535587/5000000000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((124953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c336 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((664939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -105423/500000) (δ := 2561/250000000) (ψ := 118023/125000) 202 187
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t336 : ((45340775577/1250000000000 : ℚ) : ℝ) ≤ stT202 336 := by
  have hc : ((664889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45340775577/1250000000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((664889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c337 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((970601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -607701/10000000) (δ := 2561/250000000) (ψ := 118023/125000) 202 187
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t337 : ((264346064217/5000000000000 : ℚ) : ℝ) ≤ stT202 337 := by
  have hc : ((970551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).1
  have hw2 : ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((272367/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((264346064217/5000000000000 : ℚ) : ℝ)
      = ((272367/5000000 : ℚ) : ℝ) * ((970551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c338 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((937499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 888563/10000000) (δ := 10159/1000000000) (ψ := 118023/125000) 202 187
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t338 : ((63738094959/1250000000000 : ℚ) : ℝ) ≤ stT202 338 := by
  have hc : ((937449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).1
  have hw2 : ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67991/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63738094959/1250000000000 : ℚ) : ℝ)
      = ((67991/1250000 : ℚ) : ℝ) * ((937449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c339 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((579897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 476097/2000000) (δ := 2561/250000000) (ψ := 118023/125000) 202 187
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t339 : ((503887043/16000000000 : ℚ) : ℝ) ≤ stT202 339 := by
  have hc : ((579847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).1
  have hw2 : ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((869/16000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((503887043/16000000000 : ℚ) : ℝ)
      = ((869/16000 : ℚ) : ℝ) * ((579847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c340 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((23609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1933981/5000000) (δ := 10159/1000000000) (ψ := 118023/125000) 202 187
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t340 : ((6388329117/5000000000000 : ℚ) : ℝ) ≤ stT202 340 := by
  have hc : ((23559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).1
  have hw2 : ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6388329117/5000000000000 : ℚ) : ℝ)
      = ((271163/5000000 : ℚ) : ℝ) * ((23559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c341 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-269657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2675523/5000000) (δ := 10159/1000000000) (ψ := 118023/125000) 202 187
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t341 : ((-73020581571/2500000000000 : ℚ) : ℝ) ≤ stT202 341 := by
  have hc : ((-134841/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).2
  have h0 : (0:ℝ) ≤ ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73020581571/2500000000000 : ℚ) : ℝ)
      = ((541531/10000000 : ℚ) : ℝ) * ((-134841/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c342 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-917257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3414919/5000000) (δ := 2561/250000000) (ψ := 118023/125000) 202 187
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t342 : ((-496023669873/10000000000000 : ℚ) : ℝ) ≤ stT202 342 := by
  have hc : ((-917307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-496023669873/10000000000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-917307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c343 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-491911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7403677/10000000) (δ := 10151/1000000000) (ψ := 118023/125000) 202 188
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t343 : ((-166013027/3125000000 : ℚ) : ℝ) ≤ stT202 343 := by
  have hc : ((-15373/15625 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).2
  have h0 : (0:ℝ) ≤ ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166013027/3125000000 : ℚ) : ℝ)
      = ((10799/200000 : ℚ) : ℝ) * ((-15373/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c344 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-719173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5933521/10000000) (δ := 10151/1000000000) (ψ := 118023/125000) 202 188
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t344 : ((-96944787393/2500000000000 : ℚ) : ℝ) ≤ stT202 344 := by
  have hc : ((-719223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).2
  have h0 : (0:ℝ) ≤ ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96944787393/2500000000000 : ℚ) : ℝ)
      = ((134791/2500000 : ℚ) : ℝ) * ((-719223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c345 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-42913/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4467607/10000000) (δ := 10151/1000000000) (ψ := 118023/125000) 202 188
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t345 : ((-11554485293/1000000000000 : ℚ) : ℝ) ≤ stT202 345 := by
  have hc : ((-42923/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).2
  have h0 : (0:ℝ) ≤ ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11554485293/1000000000000 : ℚ) : ℝ)
      = ((269191/5000000 : ℚ) : ℝ) * ((-42923/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c346 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((2881/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1502993/5000000) (δ := 2563/250000000) (ψ := 118023/125000) 202 188
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t346 : ((7743096009/400000000000 : ℚ) : ℝ) ≤ stT202 346 := by
  have hc : ((14403/40000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7743096009/400000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((14403/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c347 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((407107/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -387139/2500000) (δ := 2563/250000000) (ψ := 118023/125000) 202 188
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t347 : ((27316626987/625000000000 : ℚ) : ℝ) ≤ stT202 347 := by
  have hc : ((203541/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27316626987/625000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((203541/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c348 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((999273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -95317/10000000) (δ := 10151/1000000000) (ψ := 118023/125000) 202 188
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t348 : ((66954935561/1250000000000 : ℚ) : ℝ) ≤ stT202 348 := by
  have hc : ((999223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).1
  have hw2 : ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66954935561/1250000000000 : ℚ) : ℝ)
      = ((67007/1250000 : ℚ) : ℝ) * ((999223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c349 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((85693/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 67689/500000) (δ := 2563/250000000) (ψ := 118023/125000) 202 188
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t349 : ((5733459057/125000000000 : ℚ) : ℝ) ≤ stT202 349 := by
  have hc : ((10711/12500 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).1
  have hw2 : ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((535287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5733459057/125000000000 : ℚ) : ℝ)
      = ((535287/10000000 : ℚ) : ℝ) * ((10711/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c350 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((87231/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1399343/5000000) (δ := 2563/250000000) (ψ := 118023/125000) 202 188
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t350 : ((23310771681/1000000000000 : ℚ) : ℝ) ≤ stT202 350 := by
  have hc : ((87221/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).1
  have hw2 : ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((267261/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23310771681/1000000000000 : ℚ) : ℝ)
      = ((267261/5000000 : ℚ) : ℝ) * ((87221/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c351 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-124679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2119751/5000000) (δ := 10151/1000000000) (ψ := 118023/125000) 202 188
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t351 : ((-66575475769/10000000000000 : ℚ) : ℝ) ≤ stT202 351 := by
  have hc : ((-124729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66575475769/10000000000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-124729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c352 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-10062/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 354761/625000) (δ := 2563/250000000) (ψ := 118023/125000) 202 188
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t352 : ((-85815720509/2500000000000 : ℚ) : ℝ) ≤ stT202 352 := by
  have hc : ((-322009/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85815720509/2500000000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-322009/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c353 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-477953/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7108811/10000000) (δ := 10151/1000000000) (ψ := 118023/125000) 202 188
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t353 : ((-127201178283/2500000000000 : ℚ) : ℝ) ≤ stT202 353 := by
  have hc : ((-238989/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).2
  have h0 : (0:ℝ) ≤ ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127201178283/2500000000000 : ℚ) : ℝ)
      = ((532247/10000000 : ℚ) : ℝ) * ((-238989/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c354 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-962867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3585279/5000000) (δ := 2029/200000000) (ψ := 118023/125000) 202 189
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t354 : ((-102357114183/2000000000000 : ℚ) : ℝ) ≤ stT202 354 := by
  have hc : ((-962917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).2
  have h0 : (0:ℝ) ≤ ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102357114183/2000000000000 : ℚ) : ℝ)
      = ((106299/2000000 : ℚ) : ℝ) * ((-962917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c355 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-332549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2873027/5000000) (δ := 2029/200000000) (ψ := 118023/125000) 202 189
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t355 : ((-17651198763/500000000000 : ℚ) : ℝ) ≤ stT202 355 := by
  have hc : ((-166287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17651198763/500000000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-166287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c356 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-6349/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4325489/10000000) (δ := 2029/200000000) (ψ := 118023/125000) 202 189
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t356 : ((-3366023649/400000000000 : ℚ) : ℝ) ≤ stT202 356 := by
  have hc : ((-6351/40000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).2
  have h0 : (0:ℝ) ≤ ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3366023649/400000000000 : ℚ) : ℝ)
      = ((529999/10000000 : ℚ) : ℝ) * ((-6351/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c357 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((7921/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -727241/2500000) (δ := 2029/200000000) (ψ := 118023/125000) 202 189
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t357 : ((6549543/312500000 : ℚ) : ℝ) ≤ stT202 357 := by
  have hc : ((99/250 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).1
  have hw2 : ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66157/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6549543/312500000 : ℚ) : ℝ)
      = ((66157/1250000 : ℚ) : ℝ) * ((99/250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c358 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((826153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -748189/5000000) (δ := 2029/200000000) (ψ := 118023/125000) 202 189
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t358 : ((109152163287/2500000000000 : ℚ) : ℝ) ≤ stT202 358 := by
  have hc : ((826103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).1
  have hw2 : ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((132129/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109152163287/2500000000000 : ℚ) : ℝ)
      = ((132129/2500000 : ℚ) : ℝ) * ((826103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c359 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((124923/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87731/10000000) (δ := 2029/200000000) (ψ := 118023/125000) 202 189
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t359 : ((263713749593/5000000000000 : ℚ) : ℝ) ≤ stT202 359 := by
  have hc : ((499667/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((263713749593/5000000000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((499667/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c360 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((172883/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 329257/2500000) (δ := 5129/500000000) (ψ := 118023/125000) 202 189
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t360 : ((45556011579/1000000000000 : ℚ) : ℝ) ≤ stT202 360 := by
  have hc : ((172873/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).1
  have hw2 : ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45556011579/1000000000000 : ℚ) : ℝ)
      = ((263523/5000000 : ℚ) : ℝ) * ((172873/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c361 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((23251/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2717847/10000000) (δ := 2029/200000000) (ψ := 118023/125000) 202 189
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t361 : ((4894413711/200000000000 : ℚ) : ℝ) ≤ stT202 361 := by
  have hc : ((46497/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4894413711/200000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((46497/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c362 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-15013/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4114829/10000000) (δ := 5129/500000000) (ψ := 118023/125000) 202 189
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t362 : ((-7895923547/2000000000000 : ℚ) : ℝ) ≤ stT202 362 := by
  have hc : ((-15023/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).2
  have h0 : (0:ℝ) ≤ ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7895923547/2000000000000 : ℚ) : ℝ)
      = ((525589/10000000 : ℚ) : ℝ) * ((-15023/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c363 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-29553/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2753961/5000000) (δ := 5129/500000000) (ψ := 118023/125000) 202 189
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t363 : ((-484769311/15625000000 : ℚ) : ℝ) ≤ stT202 363 := by
  have hc : ((-59111/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-484769311/15625000000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-59111/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c364 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-231913/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6897177/10000000) (δ := 5129/500000000) (ψ := 118023/125000) 202 189
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t364 : ((-243124254693/5000000000000 : ℚ) : ℝ) ≤ stT202 364 := by
  have hc : ((-463851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243124254693/5000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-463851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c365 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-123167/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7425319/10000000) (δ := 5083/500000000) (ψ := 118023/125000) 202 190
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t365 : ((-8058979401/156250000000 : ℚ) : ℝ) ≤ stT202 365 := by
  have hc : ((-492693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8058979401/156250000000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-492693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c366 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-749071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6043639/10000000) (δ := 5083/500000000) (ψ := 118023/125000) 202 190
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t366 : ((-391572288789/10000000000000 : ℚ) : ℝ) ≤ stT202 366 := by
  have hc : ((-749121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-391572288789/10000000000000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-749121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c367 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-291221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4665747/10000000) (δ := 10237/1000000000) (ψ := 118023/125000) 202 190
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t367 : ((-38010574229/2500000000000 : ℚ) : ℝ) ≤ stT202 367 := by
  have hc : ((-291271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38010574229/2500000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-291271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c368 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((31429/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3291591/10000000) (δ := 5083/500000000) (ψ := 118023/125000) 202 190
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t368 : ((32760479313/2500000000000 : ℚ) : ℝ) ≤ stT202 368 := by
  have hc : ((125691/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32760479313/2500000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((125691/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c369 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((28759/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1921173/10000000) (δ := 10237/1000000000) (ψ := 118023/125000) 202 190
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t369 : ((14970290303/400000000000 : ℚ) : ℝ) ≤ stT202 369 := by
  have hc : ((28757/40000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14970290303/400000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((28757/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c370 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((243877/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -554441/10000000) (δ := 10237/1000000000) (ψ := 118023/125000) 202 190
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t370 : ((2028464911/40000000000 : ℚ) : ℝ) ≤ stT202 370 := by
  have hc : ((487729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).1
  have hw2 : ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((4159/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2028464911/40000000000 : ℚ) : ℝ)
      = ((4159/80000 : ℚ) : ℝ) * ((487729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c371 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((474077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 404277/5000000) (δ := 10237/1000000000) (ψ := 118023/125000) 202 190
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t371 : ((30764434131/625000000000 : ℚ) : ℝ) ≤ stT202 371 := by
  have hc : ((118513/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).1
  have hw2 : ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((259587/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30764434131/625000000000 : ℚ) : ℝ)
      = ((259587/5000000 : ℚ) : ℝ) * ((118513/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c372 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((646991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2167913/10000000) (δ := 10237/1000000000) (ψ := 118023/125000) 202 190
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t372 : ((13416909399/400000000000 : ℚ) : ℝ) ≤ stT202 372 := by
  have hc : ((646941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).1
  have hw2 : ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((20739/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13416909399/400000000000 : ℚ) : ℝ)
      = ((20739/400000 : ℚ) : ℝ) * ((646941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c373 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((160643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 880909/2500000) (δ := 10237/1000000000) (ψ := 118023/125000) 202 190
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t373 : ((4157592177/500000000000 : ℚ) : ℝ) ≤ stT202 373 := by
  have hc : ((160593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).1
  have hw2 : ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25889/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4157592177/500000000000 : ℚ) : ℝ)
      = ((25889/500000 : ℚ) : ℝ) * ((160593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c374 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-370431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4875673/10000000) (δ := 5083/500000000) (ψ := 118023/125000) 202 190
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t374 : ((-5986602479/312500000000 : ℚ) : ℝ) ≤ stT202 374 := by
  have hc : ((-370481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5986602479/312500000000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-370481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c375 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-794919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3112087/5000000) (δ := 10237/1000000000) (ψ := 118023/125000) 202 190
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t375 : ((-205260200831/5000000000000 : ℚ) : ℝ) ≤ stT202 375 := by
  have hc : ((-794969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).2
  have h0 : (0:ℝ) ≤ ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205260200831/5000000000000 : ℚ) : ℝ)
      = ((258199/5000000 : ℚ) : ℝ) * ((-794969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c376 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-124189/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94613/125000) (δ := 5083/500000000) (ψ := 118023/125000) 202 190
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t376 : ((-256195426291/5000000000000 : ℚ) : ℝ) ≤ stT202 376 := by
  have hc : ((-496781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).2
  have h0 : (0:ℝ) ≤ ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-256195426291/5000000000000 : ℚ) : ℝ)
      = ((515711/10000000 : ℚ) : ℝ) * ((-496781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c377 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-228013/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6797643/10000000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 191
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t377 : ((-234878578377/5000000000000 : ℚ) : ℝ) ≤ stT202 377 := by
  have hc : ((-456051/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).2
  have h0 : (0:ℝ) ≤ ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234878578377/5000000000000 : ℚ) : ℝ)
      = ((515027/10000000 : ℚ) : ℝ) * ((-456051/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c378 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-575457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2729949/5000000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 191
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t378 : ((-59201829583/2000000000000 : ℚ) : ℝ) ≤ stT202 378 := by
  have hc : ((-575507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).2
  have h0 : (0:ℝ) ≤ ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59201829583/2000000000000 : ℚ) : ℝ)
      = ((102869/2000000 : ℚ) : ℝ) * ((-575507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c379 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-127/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2062819/5000000) (δ := 1013/100000000) (ψ := 118023/125000) 202 191
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t379 : ((-815958441/200000000000 : ℚ) : ℝ) ≤ stT202 379 := by
  have hc : ((-3177/40000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-815958441/200000000000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-3177/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c380 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((87499/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2794963/10000000) (δ := 1013/100000000) (ψ := 118023/125000) 202 191
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t380 : ((44880894621/2000000000000 : ℚ) : ℝ) ≤ stT202 380 := by
  have hc : ((87489/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).1
  have hw2 : ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44880894621/2000000000000 : ℚ) : ℝ)
      = ((512989/10000000 : ℚ) : ℝ) * ((87489/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c381 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((416273/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -366943/2500000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 191
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t381 : ((5331252353/125000000000 : ℚ) : ℝ) ≤ stT202 381 := by
  have hc : ((52031/62500 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).1
  have hw2 : ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102463/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5331252353/125000000000 : ℚ) : ℝ)
      = ((102463/2000000 : ℚ) : ℝ) * ((52031/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c382 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((998341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9001/625000) (δ := 1013/100000000) (ψ := 118023/125000) 202 191
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t382 : ((127692400101/2500000000000 : ℚ) : ℝ) ≤ stT202 382 := by
  have hc : ((998291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127692400101/2500000000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((998291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c383 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((17827/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 588103/5000000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 191
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t383 : ((4447587/97656250 : ℚ) : ℝ) ≤ stT202 383 := by
  have hc : ((8913/10000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4447587/97656250 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((8913/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c384 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((271321/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 623261/2500000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 191
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t384 : ((216320409/7812500000 : ℚ) : ℝ) ≤ stT202 384 := by
  have hc : ((8478/15625 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).1
  have hw2 : ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216320409/7812500000 : ℚ) : ℝ)
      = ((51031/1000000 : ℚ) : ℝ) * ((8478/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c385 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((24099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 237903/625000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 191
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t385 : ((6134620939/2500000000000 : ℚ) : ℝ) ≤ stT202 385 := by
  have hc : ((12037/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6134620939/2500000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((12037/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c386 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-57253/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2558209/5000000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 191
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t386 : ((-116576855519/5000000000000 : ℚ) : ℝ) ≤ stT202 386 := by
  have hc : ((-229037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116576855519/5000000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-229037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c387 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-26269/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1605751/2500000) (δ := 1013/100000000) (ψ := 118023/125000) 202 191
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t387 : ((-213665420241/5000000000000 : ℚ) : ℝ) ≤ stT202 387 := by
  have hc : ((-420329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213665420241/5000000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-420329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c388 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-199739/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3863129/5000000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 191
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t388 : ((-50703686913/1000000000000 : ℚ) : ℝ) ≤ stT202 388 := by
  have hc : ((-199749/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).2
  have h0 : (0:ℝ) ≤ ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50703686913/1000000000000 : ℚ) : ℝ)
      = ((253837/5000000 : ℚ) : ℝ) * ((-199749/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c389 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-178417/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1670459/2500000) (δ := 10223/1000000000) (ψ := 118023/125000) 202 192
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t389 : ((-90466235967/2000000000000 : ℚ) : ℝ) ≤ stT202 389 := by
  have hc : ((-178427/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90466235967/2000000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-178427/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c390 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-550801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5385299/10000000) (δ := 10223/1000000000) (ψ := 118023/125000) 202 192
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t390 : ((-27893442087/1000000000000 : ℚ) : ℝ) ≤ stT202 390 := by
  have hc : ((-550851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).2
  have h0 : (0:ℝ) ≤ ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27893442087/1000000000000 : ℚ) : ℝ)
      = ((50637/1000000 : ℚ) : ℝ) * ((-550851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c391 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-32997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -818419/2000000) (δ := 10223/1000000000) (ψ := 118023/125000) 202 192
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t391 : ((-4174987971/1250000000000 : ℚ) : ℝ) ≤ stT202 391 := by
  have hc : ((-16511/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).2
  have h0 : (0:ℝ) ≤ ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4174987971/1250000000000 : ℚ) : ℝ)
      = ((252861/5000000 : ℚ) : ℝ) * ((-16511/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c392 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((4349/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2802173/10000000) (δ := 509/50000000) (ψ := 118023/125000) 202 192
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t392 : ((1098161493/50000000000 : ℚ) : ℝ) ≤ stT202 392 := by
  have hc : ((8697/20000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1098161493/50000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((8697/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c393 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((821811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -757767/5000000) (δ := 509/50000000) (ψ := 118023/125000) 202 192
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t393 : ((414523366513/10000000000000 : ℚ) : ℝ) ≤ stT202 393 := by
  have hc : ((821761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((414523366513/10000000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((821761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c394 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((995691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -116089/5000000) (δ := 10223/1000000000) (ψ := 118023/125000) 202 192
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t394 : ((31349748167/625000000000 : ℚ) : ℝ) ≤ stT202 394 := by
  have hc : ((995641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).1
  have hw2 : ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31487/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31349748167/625000000000 : ℚ) : ℝ)
      = ((31487/625000 : ℚ) : ℝ) * ((995641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c395 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((114179/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 130987/1250000) (δ := 10223/1000000000) (ψ := 118023/125000) 202 192
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t395 : ((114892951707/2500000000000 : ℚ) : ℝ) ≤ stT202 395 := by
  have hc : ((456691/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).1
  have hw2 : ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114892951707/2500000000000 : ℚ) : ℝ)
      = ((251577/5000000 : ℚ) : ℝ) * ((456691/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c396 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((298951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2324789/10000000) (δ := 509/50000000) (ψ := 118023/125000) 202 192
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t396 : ((37553923917/1250000000000 : ℚ) : ℝ) ≤ stT202 396 := by
  have hc : ((149463/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).1
  have hw2 : ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251259/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37553923917/1250000000000 : ℚ) : ℝ)
      = ((251259/5000000 : ℚ) : ℝ) * ((149463/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c397 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((131059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3598399/10000000) (δ := 509/50000000) (ψ := 118023/125000) 202 192
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t397 : ((13150290393/2000000000000 : ℚ) : ℝ) ≤ stT202 397 := by
  have hc : ((131009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).1
  have hw2 : ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((100377/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13150290393/2000000000000 : ℚ) : ℝ)
      = ((100377/2000000 : ℚ) : ℝ) * ((131009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c398 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-73581/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2434439/5000000) (δ := 509/50000000) (ψ := 118023/125000) 202 192
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t398 : ((-7377571341/400000000000 : ℚ) : ℝ) ≤ stT202 398 := by
  have hc : ((-73591/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).2
  have h0 : (0:ℝ) ≤ ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7377571341/400000000000 : ℚ) : ℝ)
      = ((100251/2000000 : ℚ) : ℝ) * ((-73591/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c399 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-386531/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49089/80000) (δ := 509/50000000) (ψ := 118023/125000) 202 192
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t399 : ((-48380092653/1250000000000 : ℚ) : ℝ) ≤ stT202 399 := by
  have hc : ((-96639/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).2
  have h0 : (0:ℝ) ≤ ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48380092653/1250000000000 : ℚ) : ℝ)
      = ((500627/10000000 : ℚ) : ℝ) * ((-96639/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c400 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-983571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 740019/1000000) (δ := 10223/1000000000) (ψ := 118023/125000) 202 192
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t400 : ((-491811483621/10000000000000 : ℚ) : ℝ) ≤ stT202 400 := by
  have hc : ((-983621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-491811483621/10000000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-983621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c401 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-948333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3523419/5000000) (δ := 10287/1000000000) (ψ := 118023/125000) 202 193
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t401 : ((-473600657391/10000000000000 : ℚ) : ℝ) ≤ stT202 401 := by
  have hc : ((-948383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).2
  have h0 : (0:ℝ) ≤ ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-473600657391/10000000000000 : ℚ) : ℝ)
      = ((499377/10000000 : ℚ) : ℝ) * ((-948383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c402 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-169463/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1157817/2000000) (δ := 10287/1000000000) (ψ := 118023/125000) 202 193
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t402 : ((-33810701201/1000000000000 : ℚ) : ℝ) ≤ stT202 402 := by
  have hc : ((-338951/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).2
  have h0 : (0:ℝ) ≤ ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33810701201/1000000000000 : ℚ) : ℝ)
      = ((99751/2000000 : ℚ) : ℝ) * ((-338951/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c403 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-48117/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4534413/10000000) (δ := 2529/250000000) (ψ := 118023/125000) 202 193
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t403 : ((-2996723909/250000000000 : ℚ) : ℝ) ≤ stT202 403 := by
  have hc : ((-48127/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2996723909/250000000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-48127/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c404 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((254807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3282871/10000000) (δ := 10287/1000000000) (ψ := 118023/125000) 202 193
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t404 : ((63373096563/5000000000000 : ℚ) : ℝ) ≤ stT202 404 := by
  have hc : ((254757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).1
  have hw2 : ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((248759/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63373096563/5000000000000 : ℚ) : ℝ)
      = ((248759/5000000 : ℚ) : ℝ) * ((254757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c405 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((686767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -203441/1000000) (δ := 10287/1000000000) (ψ := 118023/125000) 202 193
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t405 : ((341231737451/10000000000000 : ℚ) : ℝ) ≤ stT202 405 := by
  have hc : ((686717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((341231737451/10000000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((686717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c406 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((950607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -78903/1000000) (δ := 2529/250000000) (ψ := 118023/125000) 202 193
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t406 : ((471752884087/10000000000000 : ℚ) : ℝ) ≤ stT202 406 := by
  have hc : ((950557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((471752884087/10000000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((950557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c407 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((983609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45327/1000000) (δ := 2529/250000000) (ψ := 118023/125000) 202 193
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t407 : ((487531508679/10000000000000 : ℚ) : ℝ) ≤ stT202 407 := by
  have hc : ((983559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((487531508679/10000000000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((983559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c408 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((389723/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 84627/500000) (δ := 2529/250000000) (ψ := 118023/125000) 202 193
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t408 : ((96464478977/2500000000000 : ℚ) : ℝ) ≤ stT202 408 := by
  have hc : ((194849/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96464478977/2500000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((194849/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c409 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((388759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 146439/500000) (δ := 2529/250000000) (ψ := 118023/125000) 202 193
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t409 : ((48051040453/2500000000000 : ℚ) : ℝ) ≤ stT202 409 := by
  have hc : ((388709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48051040453/2500000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((388709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c410 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-93861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 416199/1000000) (δ := 2529/250000000) (ψ := 118023/125000) 202 193
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t410 : ((-9275871203/2000000000000 : ℚ) : ℝ) ≤ stT202 410 := by
  have hc : ((-93911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).2
  have h0 : (0:ℝ) ≤ ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9275871203/2000000000000 : ℚ) : ℝ)
      = ((98773/2000000 : ℚ) : ℝ) * ((-93911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c411 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-55311/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5392221/10000000) (δ := 10287/1000000000) (ψ := 118023/125000) 202 193
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t411 : ((-426334241/15625000000 : ℚ) : ℝ) ≤ stT202 411 := by
  have hc : ((-13829/25000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-426334241/15625000000 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-13829/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c412 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-880527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6619421/10000000) (δ := 2529/250000000) (ψ := 118023/125000) 202 193
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t412 : ((-86765893541/2000000000000 : ℚ) : ℝ) ≤ stT202 412 := by
  have hc : ((-880577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).2
  have h0 : (0:ℝ) ≤ ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86765893541/2000000000000 : ℚ) : ℝ)
      = ((98533/2000000 : ℚ) : ℝ) * ((-880577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c413 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-999991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3921821/5000000) (δ := 2529/250000000) (ψ := 118023/125000) 202 193
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t413 : ((-123022043697/2500000000000 : ℚ) : ℝ) ≤ stT202 413 := by
  have hc : ((-1000041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123022043697/2500000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-1000041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c414 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-884963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6643029/10000000) (δ := 5097/500000000) (ψ := 118023/125000) 202 194
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t414 : ((-217480439581/5000000000000 : ℚ) : ℝ) ≤ stT202 414 := by
  have hc : ((-885013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217480439581/5000000000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-885013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c415 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-4511/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2712333/5000000) (δ := 5097/500000000) (ψ := 118023/125000) 202 194
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t415 : ((-11072802717/400000000000 : ℚ) : ℝ) ≤ stT202 415 := by
  have hc : ((-22557/40000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11072802717/400000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-22557/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c416 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-112677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4209283/10000000) (δ := 10209/1000000000) (ψ := 118023/125000) 202 194
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t416 : ((-55269033557/10000000000000 : ℚ) : ℝ) ≤ stT202 416 := by
  have hc : ((-112727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55269033557/10000000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-112727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c417 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((363559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1498389/5000000) (δ := 10209/1000000000) (ψ := 118023/125000) 202 194
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t417 : ((89005542159/5000000000000 : ℚ) : ℝ) ≤ stT202 417 := by
  have hc : ((363509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).1
  have hw2 : ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((244851/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89005542159/5000000000000 : ℚ) : ℝ)
      = ((244851/5000000 : ℚ) : ℝ) * ((363509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c418 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((755171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -893601/5000000) (δ := 10209/1000000000) (ψ := 118023/125000) 202 194
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t418 : ((73868201583/2000000000000 : ℚ) : ℝ) ≤ stT202 418 := by
  have hc : ((755121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).1
  have hw2 : ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((97823/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73868201583/2000000000000 : ℚ) : ℝ)
      = ((97823/2000000 : ℚ) : ℝ) * ((755121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c419 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((486581/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72563/1250000) (δ := 5097/500000000) (ψ := 118023/125000) 202 194
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t419 : ((59424422309/1250000000000 : ℚ) : ℝ) ≤ stT202 419 := by
  have hc : ((121639/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59424422309/1250000000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((121639/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c420 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((969079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 124663/2000000) (δ := 5097/500000000) (ψ := 118023/125000) 202 194
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t420 : ((9456754011/200000000000 : ℚ) : ℝ) ≤ stT202 420 := by
  have hc : ((969029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9456754011/200000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((969029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c421 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((745373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 364851/2000000) (δ := 10209/1000000000) (ψ := 118023/125000) 202 194
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t421 : ((36324807051/1000000000000 : ℚ) : ℝ) ≤ stT202 421 := by
  have hc : ((745323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36324807051/1000000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((745323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c422 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((88501/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94449/312500) (δ := 5097/500000000) (ψ := 118023/125000) 202 194
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t422 : ((10768873473/625000000000 : ℚ) : ℝ) ≤ stT202 422 := by
  have hc : ((176977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10768873473/625000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((176977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c423 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-115983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2108801/5000000) (δ := 5097/500000000) (ψ := 118023/125000) 202 194
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t423 : ((-56417217161/10000000000000 : ℚ) : ℝ) ≤ stT202 423 := by
  have hc : ((-116033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).2
  have h0 : (0:ℝ) ≤ ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56417217161/10000000000000 : ℚ) : ℝ)
      = ((486217/10000000 : ℚ) : ℝ) * ((-116033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c424 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-559039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2705029/5000000) (δ := 10209/1000000000) (ψ := 118023/125000) 202 194
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t424 : ((-271517659227/10000000000000 : ℚ) : ℝ) ≤ stT202 424 := by
  have hc : ((-559089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).2
  have h0 : (0:ℝ) ≤ ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-271517659227/10000000000000 : ℚ) : ℝ)
      = ((485643/10000000 : ℚ) : ℝ) * ((-559089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c425 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-438379/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6599687/10000000) (δ := 5097/500000000) (ψ := 118023/125000) 202 194
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t425 : ((-3322773517/78125000000 : ℚ) : ℝ) ≤ stT202 425 := by
  have hc : ((-109601/125000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3322773517/78125000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-109601/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c426 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-249909/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3893269/5000000) (δ := 5097/500000000) (ψ := 118023/125000) 202 194
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t426 : ((-121087466593/2500000000000 : ℚ) : ℝ) ≤ stT202 426 := by
  have hc : ((-499843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121087466593/2500000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-499843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c427 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-450949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -842169/1250000) (δ := 5051/500000000) (ψ := 118023/125000) 202 195
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t427 : ((-54560412929/1250000000000 : ℚ) : ℝ) ≤ stT202 427 := by
  have hc : ((-225487/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54560412929/1250000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-225487/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c428 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-18953/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5556107/10000000) (δ := 10301/1000000000) (ψ := 118023/125000) 202 195
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t428 : ((-146592766737/5000000000000 : ℚ) : ℝ) ≤ stT202 428 := by
  have hc : ((-303273/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146592766737/5000000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-303273/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c429 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-35849/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2188769/5000000) (δ := 10301/1000000000) (ψ := 118023/125000) 202 195
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t429 : ((-3462580899/400000000000 : ℚ) : ℝ) ≤ stT202 429 := by
  have hc : ((-35859/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3462580899/400000000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-35859/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c430 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((143023/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1600873/5000000) (δ := 5051/500000000) (ψ := 118023/125000) 202 195
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t430 : ((17239910379/1250000000000 : ℚ) : ℝ) ≤ stT202 430 := by
  have hc : ((71499/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).1
  have hw2 : ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((241121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17239910379/1250000000000 : ℚ) : ℝ)
      = ((241121/5000000 : ℚ) : ℝ) * ((71499/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c431 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((21513/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -507183/2500000) (δ := 5051/500000000) (ψ := 118023/125000) 202 195
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t431 : ((165787099989/5000000000000 : ℚ) : ℝ) ≤ stT202 431 := by
  have hc : ((344183/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165787099989/5000000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((344183/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c432 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((94163/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -171679/2000000) (δ := 10301/1000000000) (ψ := 118023/125000) 202 195
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t432 : ((181207071/4000000000 : ℚ) : ℝ) ≤ stT202 432 := by
  have hc : ((47079/50000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181207071/4000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((47079/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c433 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((496179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 154633/5000000) (δ := 10301/1000000000) (ψ := 118023/125000) 202 195
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t433 : ((119218115813/2500000000000 : ℚ) : ℝ) ≤ stT202 433 := by
  have hc : ((248077/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119218115813/2500000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((248077/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c434 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((831119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7371/50000) (δ := 10301/1000000000) (ψ := 118023/125000) 202 195
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t434 : ((79785117207/2000000000000 : ℚ) : ℝ) ≤ stT202 434 := by
  have hc : ((831069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79785117207/2000000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((831069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c435 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((49359/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1318229/5000000) (δ := 5051/500000000) (ψ := 118023/125000) 202 195
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t435 : ((11831708451/500000000000 : ℚ) : ℝ) ≤ stT202 435 := by
  have hc : ((24677/50000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11831708451/500000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((24677/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c436 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((52357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3796039/10000000) (δ := 5051/500000000) (ψ := 118023/125000) 202 195
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t436 : ((25050502291/10000000000000 : ℚ) : ℝ) ≤ stT202 436 := by
  have hc : ((52307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25050502291/10000000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((52307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c437 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-398959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4952943/10000000) (δ := 10301/1000000000) (ψ := 118023/125000) 202 195
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t437 : ((-38174388057/2000000000000 : ℚ) : ℝ) ≤ stT202 437 := by
  have hc : ((-399009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).2
  have h0 : (0:ℝ) ≤ ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38174388057/2000000000000 : ℚ) : ℝ)
      = ((95673/2000000 : ℚ) : ℝ) * ((-399009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c438 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-765689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 763409/1250000) (δ := 10301/1000000000) (ψ := 118023/125000) 202 195
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t438 : ((-365884643241/10000000000000 : ℚ) : ℝ) ≤ stT202 438 := by
  have hc : ((-765739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-365884643241/10000000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-765739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c439 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-485903/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 290357/400000) (δ := 5051/500000000) (ψ := 118023/125000) 202 195
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t439 : ((-14495050017/312500000000 : ℚ) : ℝ) ≤ stT202 439 := by
  have hc : ((-60741/62500 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14495050017/312500000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-60741/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c440 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-19511/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1825003/2500000) (δ := 5097/500000000) (ψ := 118023/125000) 202 196
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t440 : ((-290687337/6250000000 : ℚ) : ℝ) ≤ stT202 440 := by
  have hc : ((-2439/2500 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-290687337/6250000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-2439/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c441 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-777479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6153611/10000000) (δ := 10209/1000000000) (ψ := 118023/125000) 202 196
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t441 : ((-370252312039/10000000000000 : ℚ) : ℝ) ≤ stT202 441 := by
  have hc : ((-777529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-370252312039/10000000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-777529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c442 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-419703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2504893/5000000) (δ := 10209/1000000000) (ψ := 118023/125000) 202 196
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t442 : ((-49914088489/2500000000000 : ℚ) : ℝ) ≤ stT202 442 := by
  have hc : ((-419753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49914088489/2500000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-419753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c443 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((23379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3868537/10000000) (δ := 5097/500000000) (ψ := 118023/125000) 202 196
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t443 : ((5541967253/5000000000000 : ℚ) : ℝ) ≤ stT202 443 := by
  have hc : ((23329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).1
  have hw2 : ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237557/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5541967253/5000000000000 : ℚ) : ℝ)
      = ((237557/5000000 : ℚ) : ℝ) * ((23329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c444 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((11519/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2729863/10000000) (δ := 5097/500000000) (ψ := 118023/125000) 202 196
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t444 : ((10932141519/500000000000 : ℚ) : ℝ) ≤ stT202 444 := by
  have hc : ((46071/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).1
  have hw2 : ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237289/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10932141519/500000000000 : ℚ) : ℝ)
      = ((237289/5000000 : ℚ) : ℝ) * ((46071/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c445 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((803583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -398441/2500000) (δ := 10209/1000000000) (ψ := 118023/125000) 202 196
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t445 : ((76182160197/2000000000000 : ℚ) : ℝ) ≤ stT202 445 := by
  have hc : ((803533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).1
  have hw2 : ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94809/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76182160197/2000000000000 : ℚ) : ℝ)
      = ((94809/2000000 : ℚ) : ℝ) * ((803533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c446 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((491553/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -460191/10000000) (δ := 5097/500000000) (ψ := 118023/125000) 202 196
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t446 : ((29093112233/625000000000 : ℚ) : ℝ) ≤ stT202 446 := by
  have hc : ((61441/62500 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29093112233/625000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((61441/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c447 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((964217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 670807/10000000) (δ := 5097/500000000) (ψ := 118023/125000) 202 196
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t447 : ((456034600161/10000000000000 : ℚ) : ℝ) ≤ stT202 447 := by
  have hc : ((964167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((456034600161/10000000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((964167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c448 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((375991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1799331/10000000) (δ := 10209/1000000000) (ψ := 118023/125000) 202 196
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t448 : ((17762701653/500000000000 : ℚ) : ℝ) ≤ stT202 448 := by
  have hc : ((187983/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17762701653/500000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((187983/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c449 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((390049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2925279/10000000) (δ := 10209/1000000000) (ψ := 118023/125000) 202 196
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t449 : ((184051838071/10000000000000 : ℚ) : ℝ) ≤ stT202 449 := by
  have hc : ((389999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184051838071/10000000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((389999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c450 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-9737/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 253047/625000) (δ := 5097/500000000) (ψ := 118023/125000) 202 196
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t450 : ((-918956907/400000000000 : ℚ) : ℝ) ≤ stT202 450 := by
  have hc : ((-9747/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).2
  have h0 : (0:ℝ) ≤ ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-918956907/400000000000 : ℚ) : ℝ)
      = ((94281/2000000 : ℚ) : ℝ) * ((-9747/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c451 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-238441/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5169751/10000000) (δ := 5097/500000000) (ψ := 118023/125000) 202 196
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t451 : ((-28072336753/1250000000000 : ℚ) : ℝ) ≤ stT202 451 := by
  have hc : ((-119233/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28072336753/1250000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-119233/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c452 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-4051/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 251529/400000) (δ := 5097/500000000) (ψ := 118023/125000) 202 196
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t452 : ((-1524440001/40000000000 : ℚ) : ℝ) ≤ stT202 452 := by
  have hc : ((-3241/4000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1524440001/40000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-3241/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c453 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-196773/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 296171/400000) (δ := 5097/500000000) (ψ := 118023/125000) 202 196
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t453 : ((-92456721503/2000000000000 : ℚ) : ℝ) ≤ stT202 453 := by
  have hc : ((-196783/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92456721503/2000000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-196783/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c454 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-482477/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7190163/10000000) (δ := 2529/250000000) (ψ := 118023/125000) 202 197
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t454 : ((-28306221081/625000000000 : ℚ) : ℝ) ≤ stT202 454 := by
  have hc : ((-241251/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28306221081/625000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-241251/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c455 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-75837/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1519753/2500000) (δ := 10287/1000000000) (ψ := 118023/125000) 202 197
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t455 : ((-2222208521/62500000000 : ℚ) : ℝ) ≤ stT202 455 := by
  have hc : ((-37921/50000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2222208521/62500000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-37921/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c456 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-25333/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -994067/2000000) (δ := 10287/1000000000) (ψ := 118023/125000) 202 197
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t456 : ((-94917839877/5000000000000 : ℚ) : ℝ) ≤ stT202 456 := by
  have hc : ((-202689/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94917839877/5000000000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-202689/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c457 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((25141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -966033/2500000) (δ := 2529/250000000) (ψ := 118023/125000) 202 197
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t457 : ((586853399/500000000000 : ℚ) : ℝ) ≤ stT202 457 := by
  have hc : ((25091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).1
  have hw2 : ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((23389/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((586853399/500000000000 : ℚ) : ℝ)
      = ((23389/500000 : ℚ) : ℝ) * ((25091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c458 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((449919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2760303/10000000) (δ := 2529/250000000) (ψ := 118023/125000) 202 197
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t458 : ((210209837761/10000000000000 : ℚ) : ℝ) ≤ stT202 458 := by
  have hc : ((449869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).1
  have hw2 : ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((467269/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210209837761/10000000000000 : ℚ) : ℝ)
      = ((467269/10000000 : ℚ) : ℝ) * ((449869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c459 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((787817/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51839/312500) (δ := 10287/1000000000) (ψ := 118023/125000) 202 197
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t459 : ((9192453123/250000000000 : ℚ) : ℝ) ≤ stT202 459 := by
  have hc : ((787767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).1
  have hw2 : ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11669/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9192453123/250000000000 : ℚ) : ℝ)
      = ((11669/250000 : ℚ) : ℝ) * ((787767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c460 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((975029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -559867/10000000) (δ := 10287/1000000000) (ψ := 118023/125000) 202 197
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t460 : ((113646477177/2500000000000 : ℚ) : ℝ) ≤ stT202 460 := by
  have hc : ((974979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113646477177/2500000000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((974979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c461 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((977037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 536791/10000000) (δ := 10287/1000000000) (ψ := 118023/125000) 202 197
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t461 : ((227513893651/5000000000000 : ℚ) : ℝ) ≤ stT202 461 := by
  have hc : ((976987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227513893651/5000000000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((976987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c462 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((794623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 65241/400000) (δ := 10287/1000000000) (ψ := 118023/125000) 202 197
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t462 : ((184834365833/5000000000000 : ℚ) : ℝ) ≤ stT202 462 := by
  have hc : ((794573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184834365833/5000000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((794573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c463 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((463217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 340367/1250000) (δ := 10287/1000000000) (ψ := 118023/125000) 202 197
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t463 : ((215251768413/10000000000000 : ℚ) : ℝ) ≤ stT202 463 := by
  have hc : ((463167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215251768413/10000000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((463167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c464 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((45791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1906237/5000000) (δ := 2529/250000000) (ψ := 118023/125000) 202 197
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t464 : ((10617355179/5000000000000 : ℚ) : ℝ) ≤ stT202 464 := by
  have hc : ((45741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10617355179/5000000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((45741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c465 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-47417/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 612461/1250000) (δ := 10287/1000000000) (ψ := 118023/125000) 202 197
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t465 : ((-87968042127/5000000000000 : ℚ) : ℝ) ≤ stT202 465 := by
  have hc : ((-189693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).2
  have h0 : (0:ℝ) ≤ ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87968042127/5000000000000 : ℚ) : ℝ)
      = ((463739/10000000 : ℚ) : ℝ) * ((-189693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c466 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-1833/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5984529/10000000) (δ := 10287/1000000000) (ψ := 118023/125000) 202 197
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t466 : ((-679344393/20000000000 : ℚ) : ℝ) ≤ stT202 466 := by
  have hc : ((-2933/4000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).2
  have h0 : (0:ℝ) ≤ ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-679344393/20000000000 : ℚ) : ℝ)
      = ((231621/5000000 : ℚ) : ℝ) * ((-2933/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c467 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-475433/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7067047/10000000) (δ := 10287/1000000000) (ψ := 118023/125000) 202 197
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t467 : ((-22001581221/500000000000 : ℚ) : ℝ) ≤ stT202 467 := by
  have hc : ((-237729/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22001581221/500000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-237729/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c468 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-124141/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7560721/10000000) (δ := 509/50000000) (ψ := 118023/125000) 202 198
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t468 : ((-229548761839/5000000000000 : ℚ) : ℝ) ≤ stT202 468 := by
  have hc : ((-496589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229548761839/5000000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-496589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c469 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-853321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3241399/5000000) (δ := 10223/1000000000) (ψ := 118023/125000) 202 198
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t469 : ((-197025443109/5000000000000 : ℚ) : ℝ) ≤ stT202 469 := by
  have hc : ((-853371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-197025443109/5000000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-853371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c470 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-558091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5407199/10000000) (δ := 509/50000000) (ψ := 118023/125000) 202 198
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t470 : ((-128725733253/5000000000000 : ℚ) : ℝ) ≤ stT202 470 := by
  have hc : ((-558141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128725733253/5000000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-558141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c471 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-32407/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -270867/625000) (δ := 509/50000000) (ψ := 118023/125000) 202 198
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t471 : ((-1867121949/250000000000 : ℚ) : ℝ) ≤ stT202 471 := by
  have hc : ((-32417/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1867121949/250000000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-32417/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c472 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((52511/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3262817/10000000) (δ := 10223/1000000000) (ψ := 118023/125000) 202 198
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t472 : ((24165527787/2000000000000 : ℚ) : ℝ) ≤ stT202 472 := by
  have hc : ((52501/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24165527787/2000000000000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((52501/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c473 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((159747/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -438807/2000000) (δ := 10223/1000000000) (ψ := 118023/125000) 202 198
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t473 : ((734459231/25000000000 : ℚ) : ℝ) ≤ stT202 473 := by
  have hc : ((319469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((734459231/25000000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((319469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c474 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((56251/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -45099/400000) (δ := 10223/1000000000) (ψ := 118023/125000) 202 198
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t474 : ((41336788329/1000000000000 : ℚ) : ℝ) ≤ stT202 474 := by
  have hc : ((449983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41336788329/1000000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((449983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c475 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((999681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15797/2500000) (δ := 509/50000000) (ψ := 118023/125000) 202 198
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t475 : ((458661691361/10000000000000 : ℚ) : ℝ) ≤ stT202 475 := by
  have hc : ((999631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((458661691361/10000000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((999631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c476 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((230311/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 998827/10000000) (δ := 509/50000000) (ψ := 118023/125000) 202 198
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t476 : ((211114174353/5000000000000 : ℚ) : ℝ) ≤ stT202 476 := by
  have hc : ((460597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211114174353/5000000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((460597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c477 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((42481/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102931/500000) (δ := 509/50000000) (ψ := 118023/125000) 202 198
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t477 : ((38898519341/1250000000000 : ℚ) : ℝ) ≤ stT202 477 := by
  have hc : ((339823/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38898519341/1250000000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((339823/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c478 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((63729/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1558121/5000000) (δ := 10223/1000000000) (ψ := 118023/125000) 202 198
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t478 : ((29144369691/2000000000000 : ℚ) : ℝ) ≤ stT202 478 := by
  have hc : ((63719/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).1
  have hw2 : ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((457389/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29144369691/2000000000000 : ℚ) : ℝ)
      = ((457389/10000000 : ℚ) : ℝ) * ((63719/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c479 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-24421/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4171591/10000000) (δ := 10223/1000000000) (ψ := 118023/125000) 202 198
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t479 : ((-1395494919/312500000000 : ℚ) : ℝ) ≤ stT202 479 := by
  have hc : ((-48867/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1395494919/312500000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-48867/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c480 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-248063/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5224819/10000000) (δ := 10223/1000000000) (ψ := 118023/125000) 202 198
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t480 : ((-3538634199/156250000000 : ℚ) : ℝ) ≤ stT202 480 := by
  have hc : ((-31011/62500 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3538634199/156250000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-31011/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c481 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-807271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3137887/5000000) (δ := 509/50000000) (ψ := 118023/125000) 202 198
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t481 : ((-368106890481/10000000000000 : ℚ) : ℝ) ≤ stT202 481 := by
  have hc : ((-807321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-368106890481/10000000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-807321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c482 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-195533/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7324609/10000000) (δ := 10223/1000000000) (ψ := 118023/125000) 202 198
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t482 : ((-1391679531/31250000000 : ℚ) : ℝ) ≤ stT202 482 := by
  have hc : ((-195543/200000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).2
  have h0 : (0:ℝ) ≤ ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1391679531/31250000000 : ℚ) : ℝ)
      = ((7117/156250 : ℚ) : ℝ) * ((-195543/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c483 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-978673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3668371/5000000) (δ := 1013/100000000) (ψ := 118023/125000) 202 199
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t483 : ((-55666828071/1250000000000 : ℚ) : ℝ) ≤ stT202 483 := by
  have hc : ((-978723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).2
  have h0 : (0:ℝ) ≤ ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55666828071/1250000000000 : ℚ) : ℝ)
      = ((56877/1250000 : ℚ) : ℝ) * ((-978723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c484 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-811143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6292251/10000000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 199
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t484 : ((-184362266689/5000000000000 : ℚ) : ℝ) ≤ stT202 484 := by
  have hc : ((-811193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).2
  have h0 : (0:ℝ) ≤ ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184362266689/5000000000000 : ℚ) : ℝ)
      = ((227273/5000000 : ℚ) : ℝ) * ((-811193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c485 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-12621/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5249981/10000000) (δ := 1013/100000000) (ψ := 118023/125000) 202 199
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t485 : ((-22925893653/1000000000000 : ℚ) : ℝ) ≤ stT202 485 := by
  have hc : ((-50489/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).2
  have h0 : (0:ℝ) ≤ ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22925893653/1000000000000 : ℚ) : ℝ)
      = ((454077/10000000 : ℚ) : ℝ) * ((-50489/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c486 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-903/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2104891/5000000) (δ := 1013/100000000) (ψ := 118023/125000) 202 199
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t486 : ((-204895637/40000000000 : ℚ) : ℝ) ≤ stT202 486 := by
  have hc : ((-4517/40000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).2
  have h0 : (0:ℝ) ≤ ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204895637/40000000000 : ℚ) : ℝ)
      = ((45361/1000000 : ℚ) : ℝ) * ((-4517/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c487 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((3719/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -634351/2000000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 199
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t487 : ((13479644821/1000000000000 : ℚ) : ℝ) ≤ stT202 487 := by
  have hc : ((29747/100000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).1
  have hw2 : ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453143/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13479644821/1000000000000 : ℚ) : ℝ)
      = ((453143/10000000 : ℚ) : ℝ) * ((29747/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c488 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((656717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -266981/1250000) (δ := 1013/100000000) (ψ := 118023/125000) 202 199
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t488 : ((148629352113/5000000000000 : ℚ) : ℝ) ≤ stT202 488 := by
  have hc : ((656667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).1
  have hw2 : ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((226339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148629352113/5000000000000 : ℚ) : ℝ)
      = ((226339/5000000 : ℚ) : ℝ) * ((656667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c489 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((904391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1102113/10000000) (δ := 1013/100000000) (ψ := 118023/125000) 202 199
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t489 : ((81791313063/2000000000000 : ℚ) : ℝ) ≤ stT202 489 := by
  have hc : ((904341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).1
  have hw2 : ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90443/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81791313063/2000000000000 : ℚ) : ℝ)
      = ((90443/2000000 : ℚ) : ℝ) * ((904341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c490 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((999603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -70449/10000000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 199
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t490 : ((451551066409/10000000000000 : ℚ) : ℝ) ≤ stT202 490 := by
  have hc : ((999553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).1
  have hw2 : ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451753/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((451551066409/10000000000000 : ℚ) : ℝ)
      = ((451753/10000000 : ℚ) : ℝ) * ((999553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c491 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((463651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 191829/2000000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 199
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t491 : ((104615584209/2500000000000 : ℚ) : ℝ) ≤ stT202 491 := by
  have hc : ((231813/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).1
  have hw2 : ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451293/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104615584209/2500000000000 : ℚ) : ℝ)
      = ((451293/10000000 : ℚ) : ℝ) * ((231813/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c492 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((700537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 993309/5000000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 199
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t492 : ((157901678079/5000000000000 : ℚ) : ℝ) ≤ stT202 492 := by
  have hc : ((700487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157901678079/5000000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((700487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c493 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((357891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 301197/1000000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 199
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t493 : ((161163356057/10000000000000 : ℚ) : ℝ) ≤ stT202 493 := by
  have hc : ((357841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161163356057/10000000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((357841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c494 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-43311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2017651/5000000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 199
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t494 : ((-9754533921/5000000000000 : ℚ) : ℝ) ≤ stT202 494 := by
  have hc : ((-43361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).2
  have h0 : (0:ℝ) ≤ ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9754533921/5000000000000 : ℚ) : ℝ)
      = ((224961/5000000 : ℚ) : ℝ) * ((-43361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c495 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-218297/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5056513/10000000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 199
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t495 : ((-49064267187/2500000000000 : ℚ) : ℝ) ≤ stT202 495 := by
  have hc : ((-109161/250000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).2
  have h0 : (0:ℝ) ≤ ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49064267187/2500000000000 : ℚ) : ℝ)
      = ((449467/10000000 : ℚ) : ℝ) * ((-109161/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c496 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-757507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 759463/1250000) (δ := 10273/1000000000) (ψ := 118023/125000) 202 199
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t496 : ((-170076849399/5000000000000 : ℚ) : ℝ) ≤ stT202 496 := by
  have hc : ((-757557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).2
  have h0 : (0:ℝ) ≤ ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170076849399/5000000000000 : ℚ) : ℝ)
      = ((224507/5000000 : ℚ) : ℝ) * ((-757557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c497 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-119251/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 283713/400000) (δ := 1013/100000000) (ψ := 118023/125000) 202 199
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t497 : ((-106988541149/2500000000000 : ℚ) : ℝ) ≤ stT202 497 := by
  have hc : ((-477029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106988541149/2500000000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-477029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c498 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-994847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -950011/1250000) (δ := 10237/1000000000) (ψ := 118023/125000) 202 200
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t498 : ((-445824289567/10000000000000 : ℚ) : ℝ) ≤ stT202 498 := by
  have hc : ((-994897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-445824289567/10000000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-994897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c499 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-874317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3293529/5000000) (δ := 10237/1000000000) (ψ := 118023/125000) 202 200
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t499 : ((-195710439977/5000000000000 : ℚ) : ℝ) ≤ stT202 499 := by
  have hc : ((-874367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195710439977/5000000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-874367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_c500 :
    |Real.cos (((202 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-612819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -348503/625000) (δ := 10237/1000000000) (ψ := 118023/125000) 202 200
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st202_t500 : ((-137041798483/5000000000000 : ℚ) : ℝ) ≤ stT202 500 := by
  have hc : ((-612869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((202 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((118023/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st202_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).2
  have h0 : (0:ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137041798483/5000000000000 : ℚ) : ℝ)
      = ((223607/5000000 : ℚ) : ℝ) * ((-612869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st202_p1 : ((293177/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT202 (i+1) := by
  rw [Finset.sum_range_one]
  exact st202_t1

theorem st202_p2 : ((5287573752787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT202 (i+1))
      = (∑ i ∈ Finset.range 1, stT202 (i+1)) + stT202 2 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 1
    simpa using h
  have hprev := st202_p1
  have hstep := st202_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p3 : ((3344293090931/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT202 (i+1))
      = (∑ i ∈ Finset.range 2, stT202 (i+1)) + stT202 3 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 2
    simpa using h
  have hprev := st202_p2
  have hstep := st202_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p4 : ((9024156493121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT202 (i+1))
      = (∑ i ∈ Finset.range 3, stT202 (i+1)) + stT202 4 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 3
    simpa using h
  have hprev := st202_p3
  have hstep := st202_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p5 : ((5278845452249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT202 (i+1))
      = (∑ i ∈ Finset.range 4, stT202 (i+1)) + stT202 5 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 4
    simpa using h
  have hprev := st202_p4
  have hstep := st202_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p6 : ((1368888183829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT202 (i+1))
      = (∑ i ∈ Finset.range 5, stT202 (i+1)) + stT202 6 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 5
    simpa using h
  have hprev := st202_p5
  have hstep := st202_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p7 : ((-1814578291741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT202 (i+1))
      = (∑ i ∈ Finset.range 6, stT202 (i+1)) + stT202 7 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 6
    simpa using h
  have hprev := st202_p6
  have hstep := st202_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p8 : ((-2858260857473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT202 (i+1))
      = (∑ i ∈ Finset.range 7, stT202 (i+1)) + stT202 8 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 7
    simpa using h
  have hprev := st202_p7
  have hstep := st202_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p9 : ((-6183741522569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT202 (i+1))
      = (∑ i ∈ Finset.range 8, stT202 (i+1)) + stT202 9 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 8
    simpa using h
  have hprev := st202_p8
  have hstep := st202_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p10 : ((-393072351521/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT202 (i+1))
      = (∑ i ∈ Finset.range 9, stT202 (i+1)) + stT202 10 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 9
    simpa using h
  have hprev := st202_p9
  have hstep := st202_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p11 : ((-112485935741/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT202 (i+1))
      = (∑ i ∈ Finset.range 10, stT202 (i+1)) + stT202 11 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 10
    simpa using h
  have hprev := st202_p10
  have hstep := st202_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p12 : ((-673631695873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT202 (i+1))
      = (∑ i ∈ Finset.range 11, stT202 (i+1)) + stT202 12 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 11
    simpa using h
  have hprev := st202_p11
  have hstep := st202_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p13 : ((-2385398683551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT202 (i+1))
      = (∑ i ∈ Finset.range 12, stT202 (i+1)) + stT202 13 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 12
    simpa using h
  have hprev := st202_p12
  have hstep := st202_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p14 : ((-3313388714637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT202 (i+1))
      = (∑ i ∈ Finset.range 13, stT202 (i+1)) + stT202 14 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 13
    simpa using h
  have hprev := st202_p13
  have hstep := st202_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p15 : ((-223859070773/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT202 (i+1))
      = (∑ i ∈ Finset.range 14, stT202 (i+1)) + stT202 15 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 14
    simpa using h
  have hprev := st202_p14
  have hstep := st202_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p16 : ((274321429227/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT202 (i+1))
      = (∑ i ∈ Finset.range 15, stT202 (i+1)) + stT202 16 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 15
    simpa using h
  have hprev := st202_p15
  have hstep := st202_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p17 : ((3600683935767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT202 (i+1))
      = (∑ i ∈ Finset.range 16, stT202 (i+1)) + stT202 17 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 16
    simpa using h
  have hprev := st202_p16
  have hstep := st202_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p18 : ((3942239993787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT202 (i+1))
      = (∑ i ∈ Finset.range 17, stT202 (i+1)) + stT202 18 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 17
    simpa using h
  have hprev := st202_p17
  have hstep := st202_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p19 : ((1653824271261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT202 (i+1))
      = (∑ i ∈ Finset.range 18, stT202 (i+1)) + stT202 19 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 18
    simpa using h
  have hprev := st202_p18
  have hstep := st202_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p20 : ((177930282957/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT202 (i+1))
      = (∑ i ∈ Finset.range 19, stT202 (i+1)) + stT202 20 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 19
    simpa using h
  have hprev := st202_p19
  have hstep := st202_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p21 : ((159970949787/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT202 (i+1))
      = (∑ i ∈ Finset.range 20, stT202 (i+1)) + stT202 21 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 20
    simpa using h
  have hprev := st202_p20
  have hstep := st202_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p22 : ((1449285606873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT202 (i+1))
      = (∑ i ∈ Finset.range 21, stT202 (i+1)) + stT202 22 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 21
    simpa using h
  have hprev := st202_p21
  have hstep := st202_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p23 : ((428015288599/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT202 (i+1))
      = (∑ i ∈ Finset.range 22, stT202 (i+1)) + stT202 23 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 22
    simpa using h
  have hprev := st202_p22
  have hstep := st202_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p24 : ((933463302537/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT202 (i+1))
      = (∑ i ∈ Finset.range 23, stT202 (i+1)) + stT202 24 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 23
    simpa using h
  have hprev := st202_p23
  have hstep := st202_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p25 : ((272293670469/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT202 (i+1))
      = (∑ i ∈ Finset.range 24, stT202 (i+1)) + stT202 25 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 24
    simpa using h
  have hprev := st202_p24
  have hstep := st202_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p26 : ((137814109257/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT202 (i+1))
      = (∑ i ∈ Finset.range 25, stT202 (i+1)) + stT202 26 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 25
    simpa using h
  have hprev := st202_p25
  have hstep := st202_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p27 : ((448695135639/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT202 (i+1))
      = (∑ i ∈ Finset.range 26, stT202 (i+1)) + stT202 27 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 26
    simpa using h
  have hprev := st202_p26
  have hstep := st202_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p28 : ((1833049647677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT202 (i+1))
      = (∑ i ∈ Finset.range 27, stT202 (i+1)) + stT202 28 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 27
    simpa using h
  have hprev := st202_p27
  have hstep := st202_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p29 : ((160207070469/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT202 (i+1))
      = (∑ i ∈ Finset.range 28, stT202 (i+1)) + stT202 29 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 28
    simpa using h
  have hprev := st202_p28
  have hstep := st202_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p30 : ((5735936276161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT202 (i+1))
      = (∑ i ∈ Finset.range 29, stT202 (i+1)) + stT202 30 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 29
    simpa using h
  have hprev := st202_p29
  have hstep := st202_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p31 : ((5735738710221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT202 (i+1))
      = (∑ i ∈ Finset.range 30, stT202 (i+1)) + stT202 31 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 30
    simpa using h
  have hprev := st202_p30
  have hstep := st202_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p32 : ((5506289624689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT202 (i+1))
      = (∑ i ∈ Finset.range 31, stT202 (i+1)) + stT202 32 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 31
    simpa using h
  have hprev := st202_p31
  have hstep := st202_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p33 : ((2698485284933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT202 (i+1))
      = (∑ i ∈ Finset.range 32, stT202 (i+1)) + stT202 33 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 32
    simpa using h
  have hprev := st202_p32
  have hstep := st202_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p34 : ((2860462188213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT202 (i+1))
      = (∑ i ∈ Finset.range 33, stT202 (i+1)) + stT202 34 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 33
    simpa using h
  have hprev := st202_p33
  have hstep := st202_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p35 : ((669993893787/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT202 (i+1))
      = (∑ i ∈ Finset.range 34, stT202 (i+1)) + stT202 35 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 34
    simpa using h
  have hprev := st202_p34
  have hstep := st202_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p36 : ((1032435830923/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT202 (i+1))
      = (∑ i ∈ Finset.range 35, stT202 (i+1)) + stT202 36 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 35
    simpa using h
  have hprev := st202_p35
  have hstep := st202_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p37 : ((4890517317321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT202 (i+1))
      = (∑ i ∈ Finset.range 36, stT202 (i+1)) + stT202 37 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 36
    simpa using h
  have hprev := st202_p36
  have hstep := st202_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p38 : ((511956338973/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT202 (i+1))
      = (∑ i ∈ Finset.range 37, stT202 (i+1)) + stT202 38 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 37
    simpa using h
  have hprev := st202_p37
  have hstep := st202_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p39 : ((4573892120667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT202 (i+1))
      = (∑ i ∈ Finset.range 38, stT202 (i+1)) + stT202 39 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 38
    simpa using h
  have hprev := st202_p38
  have hstep := st202_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p40 : ((7661341237183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT202 (i+1))
      = (∑ i ∈ Finset.range 39, stT202 (i+1)) + stT202 40 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 39
    simpa using h
  have hprev := st202_p39
  have hstep := st202_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p41 : ((7774354773451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT202 (i+1))
      = (∑ i ∈ Finset.range 40, stT202 (i+1)) + stT202 41 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 40
    simpa using h
  have hprev := st202_p40
  have hstep := st202_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p42 : ((9312018018611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT202 (i+1))
      = (∑ i ∈ Finset.range 41, stT202 (i+1)) + stT202 42 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 41
    simpa using h
  have hprev := st202_p41
  have hstep := st202_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p43 : ((9499981569771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT202 (i+1))
      = (∑ i ∈ Finset.range 42, stT202 (i+1)) + stT202 43 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 42
    simpa using h
  have hprev := st202_p42
  have hstep := st202_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p44 : ((7994637663447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT202 (i+1))
      = (∑ i ∈ Finset.range 43, stT202 (i+1)) + stT202 44 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 43
    simpa using h
  have hprev := st202_p43
  have hstep := st202_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p45 : ((2042430790277/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT202 (i+1))
      = (∑ i ∈ Finset.range 44, stT202 (i+1)) + stT202 45 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 44
    simpa using h
  have hprev := st202_p44
  have hstep := st202_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p46 : ((953311546157/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT202 (i+1))
      = (∑ i ∈ Finset.range 45, stT202 (i+1)) + stT202 46 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 45
    simpa using h
  have hprev := st202_p45
  have hstep := st202_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p47 : ((213242279103/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT202 (i+1))
      = (∑ i ∈ Finset.range 46, stT202 (i+1)) + stT202 47 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 46
    simpa using h
  have hprev := st202_p46
  have hstep := st202_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p48 : ((1003886600257/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT202 (i+1))
      = (∑ i ∈ Finset.range 47, stT202 (i+1)) + stT202 48 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 47
    simpa using h
  have hprev := st202_p47
  have hstep := st202_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p49 : ((11790765477/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT202 (i+1))
      = (∑ i ∈ Finset.range 48, stT202 (i+1)) + stT202 49 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 48
    simpa using h
  have hprev := st202_p48
  have hstep := st202_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p50 : ((4196348493383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT202 (i+1))
      = (∑ i ∈ Finset.range 49, stT202 (i+1)) + stT202 50 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 49
    simpa using h
  have hprev := st202_p49
  have hstep := st202_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p51 : ((834719345539/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT202 (i+1))
      = (∑ i ∈ Finset.range 50, stT202 (i+1)) + stT202 51 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 50
    simpa using h
  have hprev := st202_p50
  have hstep := st202_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p52 : ((935469506539/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT202 (i+1))
      = (∑ i ∈ Finset.range 51, stT202 (i+1)) + stT202 52 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 51
    simpa using h
  have hprev := st202_p51
  have hstep := st202_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p53 : ((124731709753/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT202 (i+1))
      = (∑ i ∈ Finset.range 52, stT202 (i+1)) + stT202 53 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 52
    simpa using h
  have hprev := st202_p52
  have hstep := st202_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p54 : ((911889407191/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT202 (i+1))
      = (∑ i ∈ Finset.range 53, stT202 (i+1)) + stT202 54 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 53
    simpa using h
  have hprev := st202_p53
  have hstep := st202_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p55 : ((856531654231/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT202 (i+1))
      = (∑ i ∈ Finset.range 54, stT202 (i+1)) + stT202 55 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 54
    simpa using h
  have hprev := st202_p54
  have hstep := st202_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p56 : ((4232461235007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT202 (i+1))
      = (∑ i ∈ Finset.range 55, stT202 (i+1)) + stT202 56 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 55
    simpa using h
  have hprev := st202_p55
  have hstep := st202_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p57 : ((4555080805577/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT202 (i+1))
      = (∑ i ∈ Finset.range 56, stT202 (i+1)) + stT202 57 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 56
    simpa using h
  have hprev := st202_p56
  have hstep := st202_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p58 : ((4048854856127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT202 (i+1))
      = (∑ i ∈ Finset.range 57, stT202 (i+1)) + stT202 58 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 57
    simpa using h
  have hprev := st202_p57
  have hstep := st202_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p59 : ((930719583859/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT202 (i+1))
      = (∑ i ∈ Finset.range 58, stT202 (i+1)) + stT202 59 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 58
    simpa using h
  have hprev := st202_p58
  have hstep := st202_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p60 : ((1605256443709/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT202 (i+1))
      = (∑ i ∈ Finset.range 59, stT202 (i+1)) + stT202 60 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 59
    simpa using h
  have hprev := st202_p59
  have hstep := st202_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p61 : ((9303280289969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT202 (i+1))
      = (∑ i ∈ Finset.range 60, stT202 (i+1)) + stT202 61 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 60
    simpa using h
  have hprev := st202_p60
  have hstep := st202_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p62 : ((64499429167/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT202 (i+1))
      = (∑ i ∈ Finset.range 61, stT202 (i+1)) + stT202 62 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 61
    simpa using h
  have hprev := st202_p61
  have hstep := st202_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p63 : ((1852790391591/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT202 (i+1))
      = (∑ i ∈ Finset.range 62, stT202 (i+1)) + stT202 63 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 62
    simpa using h
  have hprev := st202_p62
  have hstep := st202_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p64 : ((4043762383407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT202 (i+1))
      = (∑ i ∈ Finset.range 63, stT202 (i+1)) + stT202 64 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 63
    simpa using h
  have hprev := st202_p63
  have hstep := st202_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p65 : ((4629387258069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT202 (i+1))
      = (∑ i ∈ Finset.range 64, stT202 (i+1)) + stT202 65 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 64
    simpa using h
  have hprev := st202_p64
  have hstep := st202_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p66 : ((4037469776529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT202 (i+1))
      = (∑ i ∈ Finset.range 65, stT202 (i+1)) + stT202 66 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 65
    simpa using h
  have hprev := st202_p65
  have hstep := st202_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p67 : ((2319546187991/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT202 (i+1))
      = (∑ i ∈ Finset.range 66, stT202 (i+1)) + stT202 67 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 66
    simpa using h
  have hprev := st202_p66
  have hstep := st202_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p68 : ((8065817410467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT202 (i+1))
      = (∑ i ∈ Finset.range 67, stT202 (i+1)) + stT202 68 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 67
    simpa using h
  have hprev := st202_p67
  have hstep := st202_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p69 : ((9252693789519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT202 (i+1))
      = (∑ i ∈ Finset.range 68, stT202 (i+1)) + stT202 69 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 68
    simpa using h
  have hprev := st202_p68
  have hstep := st202_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p70 : ((63696307289/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT202 (i+1))
      = (∑ i ∈ Finset.range 69, stT202 (i+1)) + stT202 70 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 69
    simpa using h
  have hprev := st202_p69
  have hstep := st202_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p71 : ((567277684437/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT202 (i+1))
      = (∑ i ∈ Finset.range 70, stT202 (i+1)) + stT202 71 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 70
    simpa using h
  have hprev := st202_p70
  have hstep := st202_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p72 : ((527204740901/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT202 (i+1))
      = (∑ i ∈ Finset.range 71, stT202 (i+1)) + stT202 72 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 71
    simpa using h
  have hprev := st202_p71
  have hstep := st202_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p73 : ((271576965799/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT202 (i+1))
      = (∑ i ∈ Finset.range 72, stT202 (i+1)) + stT202 73 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 72
    simpa using h
  have hprev := st202_p72
  have hstep := st202_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p74 : ((2222746050797/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT202 (i+1))
      = (∑ i ∈ Finset.range 73, stT202 (i+1)) + stT202 74 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 73
    simpa using h
  have hprev := st202_p73
  have hstep := st202_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p75 : ((4117782184289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT202 (i+1))
      = (∑ i ∈ Finset.range 74, stT202 (i+1)) + stT202 75 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 74
    simpa using h
  have hprev := st202_p74
  have hstep := st202_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p76 : ((462075237219/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT202 (i+1))
      = (∑ i ∈ Finset.range 75, stT202 (i+1)) + stT202 76 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 75
    simpa using h
  have hprev := st202_p75
  have hstep := st202_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p77 : ((101273022051/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT202 (i+1))
      = (∑ i ∈ Finset.range 76, stT202 (i+1)) + stT202 77 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 76
    simpa using h
  have hprev := st202_p76
  have hstep := st202_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p78 : ((907588305333/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT202 (i+1))
      = (∑ i ∈ Finset.range 77, stT202 (i+1)) + stT202 78 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 77
    simpa using h
  have hprev := st202_p77
  have hstep := st202_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p79 : ((4284378193929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT202 (i+1))
      = (∑ i ∈ Finset.range 78, stT202 (i+1)) + stT202 79 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 78
    simpa using h
  have hprev := st202_p78
  have hstep := st202_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p80 : ((4210146326499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT202 (i+1))
      = (∑ i ∈ Finset.range 79, stT202 (i+1)) + stT202 80 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 79
    simpa using h
  have hprev := st202_p79
  have hstep := st202_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p81 : ((9190027020469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT202 (i+1))
      = (∑ i ∈ Finset.range 80, stT202 (i+1)) + stT202 81 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 80
    simpa using h
  have hprev := st202_p80
  have hstep := st202_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p82 : ((8096830378273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT202 (i+1))
      = (∑ i ∈ Finset.range 81, stT202 (i+1)) + stT202 82 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 81
    simpa using h
  have hprev := st202_p81
  have hstep := st202_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p83 : ((1806429737749/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT202 (i+1))
      = (∑ i ∈ Finset.range 82, stT202 (i+1)) + stT202 83 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 82
    simpa using h
  have hprev := st202_p82
  have hstep := st202_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p84 : ((1742410686653/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT202 (i+1))
      = (∑ i ∈ Finset.range 83, stT202 (i+1)) + stT202 84 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 83
    simpa using h
  have hprev := st202_p83
  have hstep := st202_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p85 : ((823695914947/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT202 (i+1))
      = (∑ i ∈ Finset.range 84, stT202 (i+1)) + stT202 85 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 84
    simpa using h
  have hprev := st202_p84
  have hstep := st202_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p86 : ((9254055507429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT202 (i+1))
      = (∑ i ∈ Finset.range 85, stT202 (i+1)) + stT202 86 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 85
    simpa using h
  have hprev := st202_p85
  have hstep := st202_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p87 : ((4148544257871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT202 (i+1))
      = (∑ i ∈ Finset.range 86, stT202 (i+1)) + stT202 87 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 86
    simpa using h
  have hprev := st202_p86
  have hstep := st202_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p88 : ((1072667809963/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT202 (i+1))
      = (∑ i ∈ Finset.range 87, stT202 (i+1)) + stT202 88 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 87
    simpa using h
  have hprev := st202_p87
  have hstep := st202_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p89 : ((9170256672961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT202 (i+1))
      = (∑ i ∈ Finset.range 88, stT202 (i+1)) + stT202 89 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 88
    simpa using h
  have hprev := st202_p88
  have hstep := st202_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p90 : ((1015134336531/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT202 (i+1))
      = (∑ i ∈ Finset.range 89, stT202 (i+1)) + stT202 90 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 89
    simpa using h
  have hprev := st202_p89
  have hstep := st202_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p91 : ((442098088911/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT202 (i+1))
      = (∑ i ∈ Finset.range 90, stT202 (i+1)) + stT202 91 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 90
    simpa using h
  have hprev := st202_p90
  have hstep := st202_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p92 : ((2256001840071/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT202 (i+1))
      = (∑ i ∈ Finset.range 91, stT202 (i+1)) + stT202 92 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 91
    simpa using h
  have hprev := st202_p91
  have hstep := st202_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p93 : ((2021161246727/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT202 (i+1))
      = (∑ i ∈ Finset.range 92, stT202 (i+1)) + stT202 93 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 92
    simpa using h
  have hprev := st202_p92
  have hstep := st202_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p94 : ((8967284539079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT202 (i+1))
      = (∑ i ∈ Finset.range 93, stT202 (i+1)) + stT202 94 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 93
    simpa using h
  have hprev := st202_p93
  have hstep := st202_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p95 : ((1788709497787/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT202 (i+1))
      = (∑ i ∈ Finset.range 94, stT202 (i+1)) + stT202 95 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 94
    simpa using h
  have hprev := st202_p94
  have hstep := st202_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p96 : ((1616571559927/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT202 (i+1))
      = (∑ i ∈ Finset.range 95, stT202 (i+1)) + stT202 96 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 95
    simpa using h
  have hprev := st202_p95
  have hstep := st202_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p97 : ((8983032087509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT202 (i+1))
      = (∑ i ∈ Finset.range 96, stT202 (i+1)) + stT202 97 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 96
    simpa using h
  have hprev := st202_p96
  have hstep := st202_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p98 : ((22406433647/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT202 (i+1))
      = (∑ i ∈ Finset.range 97, stT202 (i+1)) + stT202 98 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 97
    simpa using h
  have hprev := st202_p97
  have hstep := st202_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p99 : ((202015310307/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT202 (i+1))
      = (∑ i ∈ Finset.range 98, stT202 (i+1)) + stT202 99 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 98
    simpa using h
  have hprev := st202_p98
  have hstep := st202_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p100 : ((8899498593393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT202 (i+1))
      = (∑ i ∈ Finset.range 99, stT202 (i+1)) + stT202 100 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 99
    simpa using h
  have hprev := st202_p99
  have hstep := st202_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p101 : ((4534903070601/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT202 (i+1))
      = (∑ i ∈ Finset.range 100, stT202 (i+1)) + stT202 101 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 100
    simpa using h
  have hprev := st202_p100
  have hstep := st202_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p102 : ((162194697537/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT202 (i+1))
      = (∑ i ∈ Finset.range 101, stT202 (i+1)) + stT202 102 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 101
    simpa using h
  have hprev := st202_p101
  have hstep := st202_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p103 : ((1740766814151/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT202 (i+1))
      = (∑ i ∈ Finset.range 102, stT202 (i+1)) + stT202 103 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 102
    simpa using h
  have hprev := st202_p102
  have hstep := st202_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p104 : ((1842030918519/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT202 (i+1))
      = (∑ i ∈ Finset.range 103, stT202 (i+1)) + stT202 104 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 103
    simpa using h
  have hprev := st202_p103
  have hstep := st202_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p105 : ((257813773221/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT202 (i+1))
      = (∑ i ∈ Finset.range 104, stT202 (i+1)) + stT202 105 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 104
    simpa using h
  have hprev := st202_p104
  have hstep := st202_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p106 : ((8408095037267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT202 (i+1))
      = (∑ i ∈ Finset.range 105, stT202 (i+1)) + stT202 106 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 105
    simpa using h
  have hprev := st202_p105
  have hstep := st202_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p107 : ((1852256225383/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT202 (i+1))
      = (∑ i ∈ Finset.range 106, stT202 (i+1)) + stT202 107 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 106
    simpa using h
  have hprev := st202_p106
  have hstep := st202_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p108 : ((4286237940169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT202 (i+1))
      = (∑ i ∈ Finset.range 107, stT202 (i+1)) + stT202 108 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 107
    simpa using h
  have hprev := st202_p107
  have hstep := st202_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p109 : ((40641686237/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT202 (i+1))
      = (∑ i ∈ Finset.range 108, stT202 (i+1)) + stT202 109 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 108
    simpa using h
  have hprev := st202_p108
  have hstep := st202_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p110 : ((1132646744677/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT202 (i+1))
      = (∑ i ∈ Finset.range 109, stT202 (i+1)) + stT202 110 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 109
    simpa using h
  have hprev := st202_p109
  have hstep := st202_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p111 : ((4507247658067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT202 (i+1))
      = (∑ i ∈ Finset.range 110, stT202 (i+1)) + stT202 111 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 110
    simpa using h
  have hprev := st202_p110
  have hstep := st202_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p112 : ((4054497325371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT202 (i+1))
      = (∑ i ∈ Finset.range 111, stT202 (i+1)) + stT202 112 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 111
    simpa using h
  have hprev := st202_p111
  have hstep := st202_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p113 : ((4286056964451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT202 (i+1))
      = (∑ i ∈ Finset.range 112, stT202 (i+1)) + stT202 113 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 112
    simpa using h
  have hprev := st202_p112
  have hstep := st202_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p114 : ((9273884893797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT202 (i+1))
      = (∑ i ∈ Finset.range 113, stT202 (i+1)) + stT202 114 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 113
    simpa using h
  have hprev := st202_p113
  have hstep := st202_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p115 : ((8533550524197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT202 (i+1))
      = (∑ i ∈ Finset.range 114, stT202 (i+1)) + stT202 115 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 114
    simpa using h
  have hprev := st202_p114
  have hstep := st202_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p116 : ((4054219486727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT202 (i+1))
      = (∑ i ∈ Finset.range 115, stT202 (i+1)) + stT202 116 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 115
    simpa using h
  have hprev := st202_p115
  have hstep := st202_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p117 : ((4494073011977/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT202 (i+1))
      = (∑ i ∈ Finset.range 116, stT202 (i+1)) + stT202 117 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 116
    simpa using h
  have hprev := st202_p116
  have hstep := st202_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p118 : ((114230360111/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT202 (i+1))
      = (∑ i ∈ Finset.range 117, stT202 (i+1)) + stT202 118 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 117
    simpa using h
  have hprev := st202_p117
  have hstep := st202_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p119 : ((4111050994337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT202 (i+1))
      = (∑ i ∈ Finset.range 118, stT202 (i+1)) + stT202 119 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 118
    simpa using h
  have hprev := st202_p118
  have hstep := st202_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p120 : ((2075891398651/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT202 (i+1))
      = (∑ i ∈ Finset.range 119, stT202 (i+1)) + stT202 120 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 119
    simpa using h
  have hprev := st202_p119
  have hstep := st202_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p121 : ((2298846630241/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT202 (i+1))
      = (∑ i ∈ Finset.range 120, stT202 (i+1)) + stT202 121 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 120
    simpa using h
  have hprev := st202_p120
  have hstep := st202_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p122 : ((2234821523197/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT202 (i+1))
      = (∑ i ∈ Finset.range 121, stT202 (i+1)) + stT202 122 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 121
    simpa using h
  have hprev := st202_p121
  have hstep := st202_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p123 : ((4048472538559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT202 (i+1))
      = (∑ i ∈ Finset.range 122, stT202 (i+1)) + stT202 123 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 122
    simpa using h
  have hprev := st202_p122
  have hstep := st202_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p124 : ((66180212491/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT202 (i+1))
      = (∑ i ∈ Finset.range 123, stT202 (i+1)) + stT202 124 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 123
    simpa using h
  have hprev := st202_p123
  have hstep := st202_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p125 : ((9263766544003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT202 (i+1))
      = (∑ i ∈ Finset.range 124, stT202 (i+1)) + stT202 125 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 124
    simpa using h
  have hprev := st202_p124
  have hstep := st202_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p126 : ((1764174361619/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT202 (i+1))
      = (∑ i ∈ Finset.range 125, stT202 (i+1)) + stT202 126 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 125
    simpa using h
  have hprev := st202_p125
  have hstep := st202_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p127 : ((2015653872667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT202 (i+1))
      = (∑ i ∈ Finset.range 126, stT202 (i+1)) + stT202 127 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 126
    simpa using h
  have hprev := st202_p126
  have hstep := st202_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p128 : ((68255510417/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT202 (i+1))
      = (∑ i ∈ Finset.range 127, stT202 (i+1)) + stT202 128 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 127
    simpa using h
  have hprev := st202_p127
  have hstep := st202_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p129 : ((371095259183/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT202 (i+1))
      = (∑ i ∈ Finset.range 128, stT202 (i+1)) + stT202 129 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 128
    simpa using h
  have hprev := st202_p128
  have hstep := st202_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p130 : ((551178604097/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT202 (i+1))
      = (∑ i ∈ Finset.range 129, stT202 (i+1)) + stT202 130 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 129
    simpa using h
  have hprev := st202_p129
  have hstep := st202_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p131 : ((8063732781857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT202 (i+1))
      = (∑ i ∈ Finset.range 130, stT202 (i+1)) + stT202 131 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 130
    simpa using h
  have hprev := st202_p130
  have hstep := st202_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p132 : ((8475245265153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT202 (i+1))
      = (∑ i ∈ Finset.range 131, stT202 (i+1)) + stT202 132 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 131
    simpa using h
  have hprev := st202_p131
  have hstep := st202_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p133 : ((4628697896221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT202 (i+1))
      = (∑ i ∈ Finset.range 132, stT202 (i+1)) + stT202 133 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 132
    simpa using h
  have hprev := st202_p132
  have hstep := st202_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p134 : ((4465032730957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT202 (i+1))
      = (∑ i ∈ Finset.range 133, stT202 (i+1)) + stT202 134 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 133
    simpa using h
  have hprev := st202_p133
  have hstep := st202_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p135 : ((2028237572097/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT202 (i+1))
      = (∑ i ∈ Finset.range 134, stT202 (i+1)) + stT202 135 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 134
    simpa using h
  have hprev := st202_p134
  have hstep := st202_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p136 : ((1039551677209/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT202 (i+1))
      = (∑ i ∈ Finset.range 135, stT202 (i+1)) + stT202 136 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 135
    simpa using h
  have hprev := st202_p135
  have hstep := st202_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p137 : ((2290325181171/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT202 (i+1))
      = (∑ i ∈ Finset.range 136, stT202 (i+1)) + stT202 137 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 136
    simpa using h
  have hprev := st202_p136
  have hstep := st202_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p138 : ((9121282281857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT202 (i+1))
      = (∑ i ∈ Finset.range 137, stT202 (i+1)) + stT202 138 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 137
    simpa using h
  have hprev := st202_p137
  have hstep := st202_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p139 : ((1654971842271/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT202 (i+1))
      = (∑ i ∈ Finset.range 138, stT202 (i+1)) + stT202 139 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 138
    simpa using h
  have hprev := st202_p138
  have hstep := st202_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p140 : ((1623359664651/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT202 (i+1))
      = (∑ i ∈ Finset.range 139, stT202 (i+1)) + stT202 140 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 139
    simpa using h
  have hprev := st202_p139
  have hstep := st202_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p141 : ((4457924438613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT202 (i+1))
      = (∑ i ∈ Finset.range 140, stT202 (i+1)) + stT202 141 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 140
    simpa using h
  have hprev := st202_p140
  have hstep := st202_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p142 : ((2322912308571/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT202 (i+1))
      = (∑ i ∈ Finset.range 141, stT202 (i+1)) + stT202 142 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 141
    simpa using h
  have hprev := st202_p141
  have hstep := st202_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p143 : ((215246340661/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT202 (i+1))
      = (∑ i ∈ Finset.range 142, stT202 (i+1)) + stT202 143 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 142
    simpa using h
  have hprev := st202_p142
  have hstep := st202_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p144 : ((401164741193/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT202 (i+1))
      = (∑ i ∈ Finset.range 143, stT202 (i+1)) + stT202 144 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 143
    simpa using h
  have hprev := st202_p143
  have hstep := st202_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p145 : ((2125967147053/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT202 (i+1))
      = (∑ i ∈ Finset.range 144, stT202 (i+1)) + stT202 145 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 144
    simpa using h
  have hprev := st202_p144
  have hstep := st202_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p146 : ((4627229161061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT202 (i+1))
      = (∑ i ∈ Finset.range 145, stT202 (i+1)) + stT202 146 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 145
    simpa using h
  have hprev := st202_p145
  have hstep := st202_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p147 : ((9056163856369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT202 (i+1))
      = (∑ i ∈ Finset.range 146, stT202 (i+1)) + stT202 147 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 146
    simpa using h
  have hprev := st202_p146
  have hstep := st202_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p148 : ((2058708462581/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT202 (i+1))
      = (∑ i ∈ Finset.range 147, stT202 (i+1)) + stT202 148 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 147
    simpa using h
  have hprev := st202_p147
  have hstep := st202_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p149 : ((2024238252141/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT202 (i+1))
      = (∑ i ∈ Finset.range 148, stT202 (i+1)) + stT202 149 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 148
    simpa using h
  have hprev := st202_p148
  have hstep := st202_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p150 : ((2213125007913/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT202 (i+1))
      = (∑ i ∈ Finset.range 149, stT202 (i+1)) + stT202 150 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 149
    simpa using h
  have hprev := st202_p149
  have hstep := st202_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p151 : ((582718659611/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT202 (i+1))
      = (∑ i ∈ Finset.range 150, stT202 (i+1)) + stT202 151 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 150
    simpa using h
  have hprev := st202_p150
  have hstep := st202_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p152 : ((2197758635139/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT202 (i+1))
      = (∑ i ∈ Finset.range 151, stT202 (i+1)) + stT202 152 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 151
    simpa using h
  have hprev := st202_p151
  have hstep := st202_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p153 : ((1008768741963/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT202 (i+1))
      = (∑ i ∈ Finset.range 152, stT202 (i+1)) + stT202 153 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 152
    simpa using h
  have hprev := st202_p152
  have hstep := st202_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p154 : ((4121025956927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT202 (i+1))
      = (∑ i ∈ Finset.range 153, stT202 (i+1)) + stT202 154 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 153
    simpa using h
  have hprev := st202_p153
  have hstep := st202_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p155 : ((9044293396331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT202 (i+1))
      = (∑ i ∈ Finset.range 154, stT202 (i+1)) + stT202 155 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 154
    simpa using h
  have hprev := st202_p154
  have hstep := st202_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p156 : ((9296167534571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT202 (i+1))
      = (∑ i ∈ Finset.range 155, stT202 (i+1)) + stT202 156 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 155
    simpa using h
  have hprev := st202_p155
  have hstep := st202_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p157 : ((8637498352601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT202 (i+1))
      = (∑ i ∈ Finset.range 156, stT202 (i+1)) + stT202 157 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 156
    simpa using h
  have hprev := st202_p156
  have hstep := st202_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p158 : ((8020058628779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT202 (i+1))
      = (∑ i ∈ Finset.range 157, stT202 (i+1)) + stT202 158 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 157
    simpa using h
  have hprev := st202_p157
  have hstep := st202_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p159 : ((4159319975563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT202 (i+1))
      = (∑ i ∈ Finset.range 158, stT202 (i+1)) + stT202 159 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 158
    simpa using h
  have hprev := st202_p158
  have hstep := st202_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p160 : ((4553265251677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT202 (i+1))
      = (∑ i ∈ Finset.range 159, stT202 (i+1)) + stT202 160 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 159
    simpa using h
  have hprev := st202_p159
  have hstep := st202_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p161 : ((36275591319/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT202 (i+1))
      = (∑ i ∈ Finset.range 160, stT202 (i+1)) + stT202 161 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 160
    simpa using h
  have hprev := st202_p160
  have hstep := st202_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p162 : ((8616918218139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT202 (i+1))
      = (∑ i ∈ Finset.range 161, stT202 (i+1)) + stT202 162 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 161
    simpa using h
  have hprev := st202_p161
  have hstep := st202_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p163 : ((8014075123401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT202 (i+1))
      = (∑ i ∈ Finset.range 162, stT202 (i+1)) + stT202 163 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 162
    simpa using h
  have hprev := st202_p162
  have hstep := st202_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p164 : ((8287100934393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT202 (i+1))
      = (∑ i ∈ Finset.range 163, stT202 (i+1)) + stT202 164 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 163
    simpa using h
  have hprev := st202_p163
  have hstep := st202_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p165 : ((9065479045701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT202 (i+1))
      = (∑ i ∈ Finset.range 164, stT202 (i+1)) + stT202 165 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 164
    simpa using h
  have hprev := st202_p164
  have hstep := st202_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p166 : ((9321233665251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT202 (i+1))
      = (∑ i ∈ Finset.range 165, stT202 (i+1)) + stT202 166 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 165
    simpa using h
  have hprev := st202_p165
  have hstep := st202_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p167 : ((8726069376547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT202 (i+1))
      = (∑ i ∈ Finset.range 166, stT202 (i+1)) + stT202 167 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 166
    simpa using h
  have hprev := st202_p166
  have hstep := st202_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p168 : ((1610731364253/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT202 (i+1))
      = (∑ i ∈ Finset.range 167, stT202 (i+1)) + stT202 168 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 167
    simpa using h
  have hprev := st202_p167
  have hstep := st202_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p169 : ((326456176233/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT202 (i+1))
      = (∑ i ∈ Finset.range 168, stT202 (i+1)) + stT202 169 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 168
    simpa using h
  have hprev := st202_p168
  have hstep := st202_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p170 : ((356264999057/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT202 (i+1))
      = (∑ i ∈ Finset.range 169, stT202 (i+1)) + stT202 170 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 169
    simpa using h
  have hprev := st202_p169
  have hstep := st202_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p171 : ((1169215411601/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT202 (i+1))
      = (∑ i ∈ Finset.range 170, stT202 (i+1)) + stT202 171 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 170
    simpa using h
  have hprev := st202_p170
  have hstep := st202_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p172 : ((8952982134277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT202 (i+1))
      = (∑ i ∈ Finset.range 171, stT202 (i+1)) + stT202 172 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 171
    simpa using h
  have hprev := st202_p171
  have hstep := st202_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p173 : ((8201602124481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT202 (i+1))
      = (∑ i ∈ Finset.range 172, stT202 (i+1)) + stT202 173 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 172
    simpa using h
  have hprev := st202_p172
  have hstep := st202_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p174 : ((8011813556029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT202 (i+1))
      = (∑ i ∈ Finset.range 173, stT202 (i+1)) + stT202 174 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 173
    simpa using h
  have hprev := st202_p173
  have hstep := st202_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p175 : ((8606075770237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT202 (i+1))
      = (∑ i ∈ Finset.range 174, stT202 (i+1)) + stT202 175 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 174
    simpa using h
  have hprev := st202_p174
  have hstep := st202_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p176 : ((9272952212173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT202 (i+1))
      = (∑ i ∈ Finset.range 175, stT202 (i+1)) + stT202 176 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 175
    simpa using h
  have hprev := st202_p175
  have hstep := st202_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p177 : ((4614481035749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT202 (i+1))
      = (∑ i ∈ Finset.range 176, stT202 (i+1)) + stT202 177 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 176
    simpa using h
  have hprev := st202_p176
  have hstep := st202_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p178 : ((4265638349501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT202 (i+1))
      = (∑ i ∈ Finset.range 177, stT202 (i+1)) + stT202 178 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 177
    simpa using h
  have hprev := st202_p177
  have hstep := st202_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p179 : ((798813588601/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT202 (i+1))
      = (∑ i ∈ Finset.range 178, stT202 (i+1)) + stT202 179 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 178
    simpa using h
  have hprev := st202_p178
  have hstep := st202_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p180 : ((1643371849617/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT202 (i+1))
      = (∑ i ∈ Finset.range 179, stT202 (i+1)) + stT202 180 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 179
    simpa using h
  have hprev := st202_p179
  have hstep := st202_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p181 : ((8952871940061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT202 (i+1))
      = (∑ i ∈ Finset.range 180, stT202 (i+1)) + stT202 181 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 180
    simpa using h
  have hprev := st202_p180
  have hstep := st202_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p182 : ((1873979132493/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT202 (i+1))
      = (∑ i ∈ Finset.range 181, stT202 (i+1)) + stT202 182 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 181
    simpa using h
  have hprev := st202_p181
  have hstep := st202_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p183 : ((72075637691/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT202 (i+1))
      = (∑ i ∈ Finset.range 182, stT202 (i+1)) + stT202 183 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 182
    simpa using h
  have hprev := st202_p182
  have hstep := st202_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p184 : ((1654555395399/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT202 (i+1))
      = (∑ i ∈ Finset.range 183, stT202 (i+1)) + stT202 184 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 183
    simpa using h
  have hprev := st202_p183
  have hstep := st202_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p185 : ((398091073441/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT202 (i+1))
      = (∑ i ∈ Finset.range 184, stT202 (i+1)) + stT202 185 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 184
    simpa using h
  have hprev := st202_p184
  have hstep := st202_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p186 : ((1681374476707/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT202 (i+1))
      = (∑ i ∈ Finset.range 185, stT202 (i+1)) + stT202 186 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 185
    simpa using h
  have hprev := st202_p185
  have hstep := st202_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p187 : ((9128220291223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT202 (i+1))
      = (∑ i ∈ Finset.range 186, stT202 (i+1)) + stT202 187 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 186
    simpa using h
  have hprev := st202_p186
  have hstep := st202_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p188 : ((1872742781111/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT202 (i+1))
      = (∑ i ∈ Finset.range 187, stT202 (i+1)) + stT202 188 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 187
    simpa using h
  have hprev := st202_p187
  have hstep := st202_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p189 : ((4435853731267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT202 (i+1))
      = (∑ i ∈ Finset.range 188, stT202 (i+1)) + stT202 189 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 188
    simpa using h
  have hprev := st202_p188
  have hstep := st202_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p190 : ((8166635954113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT202 (i+1))
      = (∑ i ∈ Finset.range 189, stT202 (i+1)) + stT202 190 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 189
    simpa using h
  have hprev := st202_p189
  have hstep := st202_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p191 : ((249121225959/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT202 (i+1))
      = (∑ i ∈ Finset.range 190, stT202 (i+1)) + stT202 191 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 190
    simpa using h
  have hprev := st202_p190
  have hstep := st202_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p192 : ((4240298920181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT202 (i+1))
      = (∑ i ∈ Finset.range 191, stT202 (i+1)) + stT202 192 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 191
    simpa using h
  have hprev := st202_p191
  have hstep := st202_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p193 : ((286750482211/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT202 (i+1))
      = (∑ i ∈ Finset.range 192, stT202 (i+1)) + stT202 193 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 192
    simpa using h
  have hprev := st202_p192
  have hstep := st202_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p194 : ((4682339140059/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT202 (i+1))
      = (∑ i ∈ Finset.range 193, stT202 (i+1)) + stT202 194 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 193
    simpa using h
  have hprev := st202_p193
  have hstep := st202_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p195 : ((1108098559431/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT202 (i+1))
      = (∑ i ∈ Finset.range 194, stT202 (i+1)) + stT202 195 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 194
    simpa using h
  have hprev := st202_p194
  have hstep := st202_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p196 : ((4085055170217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT202 (i+1))
      = (∑ i ∈ Finset.range 195, stT202 (i+1)) + stT202 196 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 195
    simpa using h
  have hprev := st202_p195
  have hstep := st202_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p197 : ((3977134337963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT202 (i+1))
      = (∑ i ∈ Finset.range 196, stT202 (i+1)) + stT202 197 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 196
    simpa using h
  have hprev := st202_p196
  have hstep := st202_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p198 : ((4210094478839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT202 (i+1))
      = (∑ i ∈ Finset.range 197, stT202 (i+1)) + stT202 198 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 197
    simpa using h
  have hprev := st202_p197
  have hstep := st202_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p199 : ((1139970648209/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT202 (i+1))
      = (∑ i ∈ Finset.range 198, stT202 (i+1)) + stT202 199 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 198
    simpa using h
  have hprev := st202_p198
  have hstep := st202_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p200 : ((2348182328713/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT202 (i+1))
      = (∑ i ∈ Finset.range 199, stT202 (i+1)) + stT202 200 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 199
    simpa using h
  have hprev := st202_p199
  have hstep := st202_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p201 : ((4493989251817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT202 (i+1))
      = (∑ i ∈ Finset.range 200, stT202 (i+1)) + stT202 201 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 200
    simpa using h
  have hprev := st202_p200
  have hstep := st202_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p202 : ((16181619367/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT202 (i+1))
      = (∑ i ∈ Finset.range 201, stT202 (i+1)) + stT202 202 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 201
    simpa using h
  have hprev := st202_p201
  have hstep := st202_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p203 : ((991231506601/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT202 (i+1))
      = (∑ i ∈ Finset.range 202, stT202 (i+1)) + stT202 203 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 202
    simpa using h
  have hprev := st202_p202
  have hstep := st202_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p204 : ((1030249258591/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT202 (i+1))
      = (∑ i ∈ Finset.range 203, stT202 (i+1)) + stT202 204 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 203
    simpa using h
  have hprev := st202_p203
  have hstep := st202_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p205 : ((4467647050189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT202 (i+1))
      = (∑ i ∈ Finset.range 204, stT202 (i+1)) + stT202 205 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 204
    simpa using h
  have hprev := st202_p204
  have hstep := st202_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p206 : ((2347179545629/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT202 (i+1))
      = (∑ i ∈ Finset.range 205, stT202 (i+1)) + stT202 206 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 205
    simpa using h
  have hprev := st202_p205
  have hstep := st202_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p207 : ((4601807061467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT202 (i+1))
      = (∑ i ∈ Finset.range 206, stT202 (i+1)) + stT202 207 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 206
    simpa using h
  have hprev := st202_p206
  have hstep := st202_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p208 : ((4273559396187/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT202 (i+1))
      = (∑ i ∈ Finset.range 207, stT202 (i+1)) + stT202 208 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 207
    simpa using h
  have hprev := st202_p207
  have hstep := st202_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p209 : ((3996349076217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT202 (i+1))
      = (∑ i ∈ Finset.range 208, stT202 (i+1)) + stT202 209 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 208
    simpa using h
  have hprev := st202_p208
  have hstep := st202_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p210 : ((4008220954477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT202 (i+1))
      = (∑ i ∈ Finset.range 209, stT202 (i+1)) + stT202 210 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 209
    simpa using h
  have hprev := st202_p209
  have hstep := st202_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p211 : ((4296744915631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT202 (i+1))
      = (∑ i ∈ Finset.range 210, stT202 (i+1)) + stT202 211 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 210
    simpa using h
  have hprev := st202_p210
  have hstep := st202_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p212 : ((4615839992851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT202 (i+1))
      = (∑ i ∈ Finset.range 211, stT202 (i+1)) + stT202 212 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 211
    simpa using h
  have hprev := st202_p211
  have hstep := st202_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p213 : ((4697870015023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT202 (i+1))
      = (∑ i ∈ Finset.range 212, stT202 (i+1)) + stT202 213 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 212
    simpa using h
  have hprev := st202_p212
  have hstep := st202_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p214 : ((2238269782661/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT202 (i+1))
      = (∑ i ∈ Finset.range 213, stT202 (i+1)) + stT202 214 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 213
    simpa using h
  have hprev := st202_p213
  have hstep := st202_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p215 : ((8272979394749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT202 (i+1))
      = (∑ i ∈ Finset.range 214, stT202 (i+1)) + stT202 215 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 214
    simpa using h
  have hprev := st202_p214
  have hstep := st202_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p216 : ((7912557975223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT202 (i+1))
      = (∑ i ∈ Finset.range 215, stT202 (i+1)) + stT202 216 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 215
    simpa using h
  have hprev := st202_p215
  have hstep := st202_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p217 : ((8161051536799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT202 (i+1))
      = (∑ i ∈ Finset.range 216, stT202 (i+1)) + stT202 217 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 216
    simpa using h
  have hprev := st202_p216
  have hstep := st202_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p218 : ((1101782635863/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT202 (i+1))
      = (∑ i ∈ Finset.range 217, stT202 (i+1)) + stT202 218 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 217
    simpa using h
  have hprev := st202_p217
  have hstep := st202_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p219 : ((9349191389529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT202 (i+1))
      = (∑ i ∈ Finset.range 218, stT202 (i+1)) + stT202 219 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 218
    simpa using h
  have hprev := st202_p218
  have hstep := st202_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p220 : ((9344623010329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT202 (i+1))
      = (∑ i ∈ Finset.range 219, stT202 (i+1)) + stT202 220 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 219
    simpa using h
  have hprev := st202_p219
  have hstep := st202_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p221 : ((4404127879169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT202 (i+1))
      = (∑ i ∈ Finset.range 220, stT202 (i+1)) + stT202 221 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 220
    simpa using h
  have hprev := st202_p220
  have hstep := st202_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p222 : ((8160316092439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT202 (i+1))
      = (∑ i ∈ Finset.range 221, stT202 (i+1)) + stT202 222 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 221
    simpa using h
  have hprev := st202_p221
  have hstep := st202_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p223 : ((7900163763939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT202 (i+1))
      = (∑ i ∈ Finset.range 222, stT202 (i+1)) + stT202 223 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 222
    simpa using h
  have hprev := st202_p222
  have hstep := st202_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p224 : ((1027914077703/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT202 (i+1))
      = (∑ i ∈ Finset.range 223, stT202 (i+1)) + stT202 224 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 223
    simpa using h
  have hprev := st202_p223
  have hstep := st202_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p225 : ((888076596417/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT202 (i+1))
      = (∑ i ∈ Finset.range 224, stT202 (i+1)) + stT202 225 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 224
    simpa using h
  have hprev := st202_p224
  have hstep := st202_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p226 : ((468828698907/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT202 (i+1))
      = (∑ i ∈ Finset.range 225, stT202 (i+1)) + stT202 226 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 225
    simpa using h
  have hprev := st202_p225
  have hstep := st202_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p227 : ((233572830387/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT202 (i+1))
      = (∑ i ∈ Finset.range 226, stT202 (i+1)) + stT202 227 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 226
    simpa using h
  have hprev := st202_p226
  have hstep := st202_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p228 : ((440430472261/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT202 (i+1))
      = (∑ i ∈ Finset.range 227, stT202 (i+1)) + stT202 228 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 227
    simpa using h
  have hprev := st202_p227
  have hstep := st202_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p229 : ((8168601617987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT202 (i+1))
      = (∑ i ∈ Finset.range 228, stT202 (i+1)) + stT202 229 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 228
    simpa using h
  have hprev := st202_p228
  have hstep := st202_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p230 : ((1577687181227/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT202 (i+1))
      = (∑ i ∈ Finset.range 229, stT202 (i+1)) + stT202 230 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 229
    simpa using h
  have hprev := st202_p229
  have hstep := st202_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p231 : ((4083601253687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT202 (i+1))
      = (∑ i ∈ Finset.range 230, stT202 (i+1)) + stT202 231 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 230
    simpa using h
  have hprev := st202_p230
  have hstep := st202_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p232 : ((35206090867/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT202 (i+1))
      = (∑ i ∈ Finset.range 231, stT202 (i+1)) + stT202 232 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 231
    simpa using h
  have hprev := st202_p231
  have hstep := st202_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p233 : ((2334787596471/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT202 (i+1))
      = (∑ i ∈ Finset.range 232, stT202 (i+1)) + stT202 233 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 232
    simpa using h
  have hprev := st202_p232
  have hstep := st202_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p234 : ((2350694565231/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT202 (i+1))
      = (∑ i ∈ Finset.range 233, stT202 (i+1)) + stT202 234 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 233
    simpa using h
  have hprev := st202_p233
  have hstep := st202_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p235 : ((8951514671607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT202 (i+1))
      = (∑ i ∈ Finset.range 234, stT202 (i+1)) + stT202 235 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 234
    simpa using h
  have hprev := st202_p234
  have hstep := st202_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p236 : ((518836093397/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT202 (i+1))
      = (∑ i ∈ Finset.range 235, stT202 (i+1)) + stT202 236 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 235
    simpa using h
  have hprev := st202_p235
  have hstep := st202_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p237 : ((3950043394661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT202 (i+1))
      = (∑ i ∈ Finset.range 236, stT202 (i+1)) + stT202 237 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 236
    simpa using h
  have hprev := st202_p236
  have hstep := st202_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p238 : ((4009539355219/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT202 (i+1))
      = (∑ i ∈ Finset.range 237, stT202 (i+1)) + stT202 238 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 237
    simpa using h
  have hprev := st202_p237
  have hstep := st202_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p239 : ((4287065397289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT202 (i+1))
      = (∑ i ∈ Finset.range 238, stT202 (i+1)) + stT202 239 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 238
    simpa using h
  have hprev := st202_p238
  have hstep := st202_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p240 : ((918994526053/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT202 (i+1))
      = (∑ i ∈ Finset.range 239, stT202 (i+1)) + stT202 240 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 239
    simpa using h
  have hprev := st202_p239
  have hstep := st202_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p241 : ((4728228215751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT202 (i+1))
      = (∑ i ∈ Finset.range 240, stT202 (i+1)) + stT202 241 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 240
    simpa using h
  have hprev := st202_p240
  have hstep := st202_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p242 : ((9200287454877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT202 (i+1))
      = (∑ i ∈ Finset.range 241, stT202 (i+1)) + stT202 242 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 241
    simpa using h
  have hprev := st202_p241
  have hstep := st202_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p243 : ((8592948949131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT202 (i+1))
      = (∑ i ∈ Finset.range 242, stT202 (i+1)) + stT202 243 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 242
    simpa using h
  have hprev := st202_p242
  have hstep := st202_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p244 : ((8031592488921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT202 (i+1))
      = (∑ i ∈ Finset.range 243, stT202 (i+1)) + stT202 244 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 243
    simpa using h
  have hprev := st202_p243
  have hstep := st202_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p245 : ((3938908994703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT202 (i+1))
      = (∑ i ∈ Finset.range 244, stT202 (i+1)) + stT202 245 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 244
    simpa using h
  have hprev := st202_p244
  have hstep := st202_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p246 : ((4113539467163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT202 (i+1))
      = (∑ i ∈ Finset.range 245, stT202 (i+1)) + stT202 246 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 245
    simpa using h
  have hprev := st202_p245
  have hstep := st202_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p247 : ((4426996508071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT202 (i+1))
      = (∑ i ∈ Finset.range 246, stT202 (i+1)) + stT202 247 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 246
    simpa using h
  have hprev := st202_p246
  have hstep := st202_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p248 : ((4680766638071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT202 (i+1))
      = (∑ i ∈ Finset.range 247, stT202 (i+1)) + stT202 248 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 247
    simpa using h
  have hprev := st202_p247
  have hstep := st202_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p249 : ((943315169283/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT202 (i+1))
      = (∑ i ∈ Finset.range 248, stT202 (i+1)) + stT202 249 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 248
    simpa using h
  have hprev := st202_p248
  have hstep := st202_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p250 : ((4513728865991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT202 (i+1))
      = (∑ i ∈ Finset.range 249, stT202 (i+1)) + stT202 250 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 249
    simpa using h
  have hprev := st202_p249
  have hstep := st202_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p251 : ((8397693651047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT202 (i+1))
      = (∑ i ∈ Finset.range 250, stT202 (i+1)) + stT202 251 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 250
    simpa using h
  have hprev := st202_p250
  have hstep := st202_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p252 : ((495649465523/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT202 (i+1))
      = (∑ i ∈ Finset.range 251, stT202 (i+1)) + stT202 252 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 251
    simpa using h
  have hprev := st202_p251
  have hstep := st202_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p253 : ((3953959058449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT202 (i+1))
      = (∑ i ∈ Finset.range 252, stT202 (i+1)) + stT202 253 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 252
    simpa using h
  have hprev := st202_p252
  have hstep := st202_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p254 : ((2085168771327/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT202 (i+1))
      = (∑ i ∈ Finset.range 253, stT202 (i+1)) + stT202 254 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 253
    simpa using h
  have hprev := st202_p253
  have hstep := st202_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p255 : ((448339412183/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT202 (i+1))
      = (∑ i ∈ Finset.range 254, stT202 (i+1)) + stT202 255 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 254
    simpa using h
  have hprev := st202_p254
  have hstep := st202_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p256 : ((470670568433/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT202 (i+1))
      = (∑ i ∈ Finset.range 255, stT202 (i+1)) + stT202 256 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 255
    simpa using h
  have hprev := st202_p255
  have hstep := st202_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p257 : ((4709373288053/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT202 (i+1))
      = (∑ i ∈ Finset.range 256, stT202 (i+1)) + stT202 257 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 256
    simpa using h
  have hprev := st202_p256
  have hstep := st202_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p258 : ((8982707030647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT202 (i+1))
      = (∑ i ∈ Finset.range 257, stT202 (i+1)) + stT202 258 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 257
    simpa using h
  have hprev := st202_p257
  have hstep := st202_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p259 : ((8361362506817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT202 (i+1))
      = (∑ i ∈ Finset.range 258, stT202 (i+1)) + stT202 259 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 258
    simpa using h
  have hprev := st202_p258
  have hstep := st202_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p260 : ((7913919369297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT202 (i+1))
      = (∑ i ∈ Finset.range 259, stT202 (i+1)) + stT202 260 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 259
    simpa using h
  have hprev := st202_p259
  have hstep := st202_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p261 : ((7895057658377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT202 (i+1))
      = (∑ i ∈ Finset.range 260, stT202 (i+1)) + stT202 261 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 260
    simpa using h
  have hprev := st202_p260
  have hstep := st202_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p262 : ((1662506730613/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT202 (i+1))
      = (∑ i ∈ Finset.range 261, stT202 (i+1)) + stT202 262 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 261
    simpa using h
  have hprev := st202_p261
  have hstep := st202_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p263 : ((8928047259761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT202 (i+1))
      = (∑ i ∈ Finset.range 262, stT202 (i+1)) + stT202 263 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 262
    simpa using h
  have hprev := st202_p262
  have hstep := st202_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p264 : ((4697903752179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT202 (i+1))
      = (∑ i ∈ Finset.range 263, stT202 (i+1)) + stT202 264 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 263
    simpa using h
  have hprev := st202_p263
  have hstep := st202_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p265 : ((2364233385657/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT202 (i+1))
      = (∑ i ∈ Finset.range 264, stT202 (i+1)) + stT202 265 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 264
    simpa using h
  have hprev := st202_p264
  have hstep := st202_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p266 : ((283763687229/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT202 (i+1))
      = (∑ i ∈ Finset.range 265, stT202 (i+1)) + stT202 266 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 265
    simpa using h
  have hprev := st202_p265
  have hstep := st202_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p267 : ((1695089266479/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT202 (i+1))
      = (∑ i ∈ Finset.range 266, stT202 (i+1)) + stT202 267 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 266
    simpa using h
  have hprev := st202_p266
  have hstep := st202_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p268 : ((7972442935947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT202 (i+1))
      = (∑ i ∈ Finset.range 267, stT202 (i+1)) + stT202 268 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 267
    simpa using h
  have hprev := st202_p267
  have hstep := st202_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p269 : ((7842302561841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT202 (i+1))
      = (∑ i ∈ Finset.range 268, stT202 (i+1)) + stT202 269 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 268
    simpa using h
  have hprev := st202_p268
  have hstep := st202_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p270 : ((8152284610581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT202 (i+1))
      = (∑ i ∈ Finset.range 269, stT202 (i+1)) + stT202 270 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 269
    simpa using h
  have hprev := st202_p269
  have hstep := st202_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p271 : ((8734426704149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT202 (i+1))
      = (∑ i ∈ Finset.range 270, stT202 (i+1)) + stT202 271 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 270
    simpa using h
  have hprev := st202_p270
  have hstep := st202_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p272 : ((9279187127987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT202 (i+1))
      = (∑ i ∈ Finset.range 271, stT202 (i+1)) + stT202 272 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 271
    simpa using h
  have hprev := st202_p271
  have hstep := st202_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p273 : ((9500858779461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT202 (i+1))
      = (∑ i ∈ Finset.range 272, stT202 (i+1)) + stT202 273 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 272
    simpa using h
  have hprev := st202_p272
  have hstep := st202_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p274 : ((4643002727563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT202 (i+1))
      = (∑ i ∈ Finset.range 273, stT202 (i+1)) + stT202 274 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 273
    simpa using h
  have hprev := st202_p273
  have hstep := st202_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p275 : ((8748716183287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT202 (i+1))
      = (∑ i ∈ Finset.range 274, stT202 (i+1)) + stT202 275 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 274
    simpa using h
  have hprev := st202_p274
  have hstep := st202_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p276 : ((8167272870837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT202 (i+1))
      = (∑ i ∈ Finset.range 275, stT202 (i+1)) + stT202 276 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 275
    simpa using h
  have hprev := st202_p275
  have hstep := st202_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p277 : ((1567755986351/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT202 (i+1))
      = (∑ i ∈ Finset.range 276, stT202 (i+1)) + stT202 277 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 276
    simpa using h
  have hprev := st202_p276
  have hstep := st202_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p278 : ((12684970219/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT202 (i+1))
      = (∑ i ∈ Finset.range 277, stT202 (i+1)) + stT202 278 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 277
    simpa using h
  have hprev := st202_p277
  have hstep := st202_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p279 : ((8387532896371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT202 (i+1))
      = (∑ i ∈ Finset.range 278, stT202 (i+1)) + stT202 279 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 278
    simpa using h
  have hprev := st202_p278
  have hstep := st202_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p280 : ((1796980494449/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT202 (i+1))
      = (∑ i ∈ Finset.range 279, stT202 (i+1)) + stT202 280 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 279
    simpa using h
  have hprev := st202_p279
  have hstep := st202_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p281 : ((9422613142407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT202 (i+1))
      = (∑ i ∈ Finset.range 280, stT202 (i+1)) + stT202 281 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 280
    simpa using h
  have hprev := st202_p280
  have hstep := st202_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p282 : ((2371440794121/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT202 (i+1))
      = (∑ i ∈ Finset.range 281, stT202 (i+1)) + stT202 282 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 281
    simpa using h
  have hprev := st202_p281
  have hstep := st202_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p283 : ((9145811240091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT202 (i+1))
      = (∑ i ∈ Finset.range 282, stT202 (i+1)) + stT202 283 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 282
    simpa using h
  have hprev := st202_p282
  have hstep := st202_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p284 : ((428538364821/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT202 (i+1))
      = (∑ i ∈ Finset.range 283, stT202 (i+1)) + stT202 284 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 283
    simpa using h
  have hprev := st202_p283
  have hstep := st202_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p285 : ((1005011413113/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT202 (i+1))
      = (∑ i ∈ Finset.range 284, stT202 (i+1)) + stT202 285 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 284
    simpa using h
  have hprev := st202_p284
  have hstep := st202_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p286 : ((7808291287087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT202 (i+1))
      = (∑ i ∈ Finset.range 285, stT202 (i+1)) + stT202 286 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 285
    simpa using h
  have hprev := st202_p285
  have hstep := st202_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p287 : ((3991999230757/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT202 (i+1))
      = (∑ i ∈ Finset.range 286, stT202 (i+1)) + stT202 287 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 286
    simpa using h
  have hprev := st202_p286
  have hstep := st202_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p288 : ((8481363269049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT202 (i+1))
      = (∑ i ∈ Finset.range 287, stT202 (i+1)) + stT202 288 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 287
    simpa using h
  have hprev := st202_p287
  have hstep := st202_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p289 : ((566517134629/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT202 (i+1))
      = (∑ i ∈ Finset.range 288, stT202 (i+1)) + stT202 289 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 288
    simpa using h
  have hprev := st202_p288
  have hstep := st202_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p290 : ((2364914840701/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT202 (i+1))
      = (∑ i ∈ Finset.range 289, stT202 (i+1)) + stT202 290 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 289
    simpa using h
  have hprev := st202_p289
  have hstep := st202_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p291 : ((1185633652683/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT202 (i+1))
      = (∑ i ∈ Finset.range 290, stT202 (i+1)) + stT202 291 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 290
    simpa using h
  have hprev := st202_p290
  have hstep := st202_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p292 : ((4565540519047/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT202 (i+1))
      = (∑ i ∈ Finset.range 291, stT202 (i+1)) + stT202 292 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 291
    simpa using h
  have hprev := st202_p291
  have hstep := st202_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p293 : ((8562312876483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT202 (i+1))
      = (∑ i ∈ Finset.range 292, stT202 (i+1)) + stT202 293 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 292
    simpa using h
  have hprev := st202_p292
  have hstep := st202_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p294 : ((8039077232139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT202 (i+1))
      = (∑ i ∈ Finset.range 293, stT202 (i+1)) + stT202 294 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 293
    simpa using h
  have hprev := st202_p293
  have hstep := st202_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p295 : ((974722227613/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT202 (i+1))
      = (∑ i ∈ Finset.range 294, stT202 (i+1)) + stT202 295 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 294
    simpa using h
  have hprev := st202_p294
  have hstep := st202_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p296 : ((3972550074049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT202 (i+1))
      = (∑ i ∈ Finset.range 295, stT202 (i+1)) + stT202 296 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 295
    simpa using h
  have hprev := st202_p295
  have hstep := st202_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p297 : ((4206419579401/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT202 (i+1))
      = (∑ i ∈ Finset.range 296, stT202 (i+1)) + stT202 297 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 296
    simpa using h
  have hprev := st202_p296
  have hstep := st202_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p298 : ((899148710497/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT202 (i+1))
      = (∑ i ∈ Finset.range 297, stT202 (i+1)) + stT202 298 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 297
    simpa using h
  have hprev := st202_p297
  have hstep := st202_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p299 : ((4712641374813/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT202 (i+1))
      = (∑ i ∈ Finset.range 298, stT202 (i+1)) + stT202 299 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 298
    simpa using h
  have hprev := st202_p298
  have hstep := st202_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p300 : ((297659814693/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT202 (i+1))
      = (∑ i ∈ Finset.range 299, stT202 (i+1)) + stT202 300 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 299
    simpa using h
  have hprev := st202_p299
  have hstep := st202_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p301 : ((2312392299961/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT202 (i+1))
      = (∑ i ∈ Finset.range 300, stT202 (i+1)) + stT202 301 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 300
    simpa using h
  have hprev := st202_p300
  have hstep := st202_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p302 : ((436003685417/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT202 (i+1))
      = (∑ i ∈ Finset.range 301, stT202 (i+1)) + stT202 302 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 301
    simpa using h
  have hprev := st202_p301
  have hstep := st202_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p303 : ((1633133276921/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT202 (i+1))
      = (∑ i ∈ Finset.range 302, stT202 (i+1)) + stT202 303 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 302
    simpa using h
  have hprev := st202_p302
  have hstep := st202_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p304 : ((1564635624137/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT202 (i+1))
      = (∑ i ∈ Finset.range 303, stT202 (i+1)) + stT202 304 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 303
    simpa using h
  have hprev := st202_p303
  have hstep := st202_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p305 : ((7836598100011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT202 (i+1))
      = (∑ i ∈ Finset.range 304, stT202 (i+1)) + stT202 305 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 304
    simpa using h
  have hprev := st202_p304
  have hstep := st202_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p306 : ((4099059115697/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT202 (i+1))
      = (∑ i ∈ Finset.range 305, stT202 (i+1)) + stT202 306 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 305
    simpa using h
  have hprev := st202_p305
  have hstep := st202_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p307 : ((4377086810817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT202 (i+1))
      = (∑ i ∈ Finset.range 306, stT202 (i+1)) + stT202 307 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 306
    simpa using h
  have hprev := st202_p306
  have hstep := st202_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p308 : ((4636053272787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT202 (i+1))
      = (∑ i ∈ Finset.range 307, stT202 (i+1)) + stT202 308 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 307
    simpa using h
  have hprev := st202_p307
  have hstep := st202_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p309 : ((4768935107587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT202 (i+1))
      = (∑ i ∈ Finset.range 308, stT202 (i+1)) + stT202 309 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 308
    simpa using h
  have hprev := st202_p308
  have hstep := st202_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p310 : ((590231417721/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT202 (i+1))
      = (∑ i ∈ Finset.range 309, stT202 (i+1)) + stT202 310 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 309
    simpa using h
  have hprev := st202_p309
  have hstep := st202_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p311 : ((282193854477/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT202 (i+1))
      = (∑ i ∈ Finset.range 310, stT202 (i+1)) + stT202 311 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 310
    simpa using h
  have hprev := st202_p310
  have hstep := st202_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p312 : ((4233583958631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT202 (i+1))
      = (∑ i ∈ Finset.range 311, stT202 (i+1)) + stT202 312 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 311
    simpa using h
  have hprev := st202_p311
  have hstep := st202_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p313 : ((3991335970911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT202 (i+1))
      = (∑ i ∈ Finset.range 312, stT202 (i+1)) + stT202 313 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 312
    simpa using h
  have hprev := st202_p312
  have hstep := st202_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p314 : ((7770549889449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT202 (i+1))
      = (∑ i ∈ Finset.range 313, stT202 (i+1)) + stT202 314 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 313
    simpa using h
  have hprev := st202_p313
  have hstep := st202_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p315 : ((1582747852149/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT202 (i+1))
      = (∑ i ∈ Finset.range 314, stT202 (i+1)) + stT202 315 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 314
    simpa using h
  have hprev := st202_p314
  have hstep := st202_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p316 : ((8353408243427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT202 (i+1))
      = (∑ i ∈ Finset.range 315, stT202 (i+1)) + stT202 316 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 315
    simpa using h
  have hprev := st202_p315
  have hstep := st202_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p317 : ((2228671312403/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT202 (i+1))
      = (∑ i ∈ Finset.range 316, stT202 (i+1)) + stT202 317 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 316
    simpa using h
  have hprev := st202_p316
  have hstep := st202_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p318 : ((293037339199/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT202 (i+1))
      = (∑ i ∈ Finset.range 317, stT202 (i+1)) + stT202 318 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 317
    simpa using h
  have hprev := st202_p317
  have hstep := st202_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p319 : ((2390396441601/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT202 (i+1))
      = (∑ i ∈ Finset.range 318, stT202 (i+1)) + stT202 319 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 318
    simpa using h
  have hprev := st202_p318
  have hstep := st202_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p320 : ((9398190128457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT202 (i+1))
      = (∑ i ∈ Finset.range 319, stT202 (i+1)) + stT202 320 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 319
    simpa using h
  have hprev := st202_p319
  have hstep := st202_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p321 : ((8951794446139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT202 (i+1))
      = (∑ i ∈ Finset.range 320, stT202 (i+1)) + stT202 321 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 320
    simpa using h
  have hprev := st202_p320
  have hstep := st202_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p322 : ((8394555570227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT202 (i+1))
      = (∑ i ∈ Finset.range 321, stT202 (i+1)) + stT202 322 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 321
    simpa using h
  have hprev := st202_p321
  have hstep := st202_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p323 : ((3969345997061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT202 (i+1))
      = (∑ i ∈ Finset.range 322, stT202 (i+1)) + stT202 323 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 322
    simpa using h
  have hprev := st202_p322
  have hstep := st202_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p324 : ((3877834812741/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT202 (i+1))
      = (∑ i ∈ Finset.range 323, stT202 (i+1)) + stT202 324 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 323
    simpa using h
  have hprev := st202_p323
  have hstep := st202_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p325 : ((3956285756391/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT202 (i+1))
      = (∑ i ∈ Finset.range 324, stT202 (i+1)) + stT202 325 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 324
    simpa using h
  have hprev := st202_p324
  have hstep := st202_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p326 : ((834892675191/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT202 (i+1))
      = (∑ i ∈ Finset.range 325, stT202 (i+1)) + stT202 326 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 325
    simpa using h
  have hprev := st202_p325
  have hstep := st202_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p327 : ((8901347653861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT202 (i+1))
      = (∑ i ∈ Finset.range 326, stT202 (i+1)) + stT202 327 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 326
    simpa using h
  have hprev := st202_p326
  have hstep := st202_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p328 : ((4682776610901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT202 (i+1))
      = (∑ i ∈ Finset.range 327, stT202 (i+1)) + stT202 328 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 327
    simpa using h
  have hprev := st202_p327
  have hstep := st202_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p329 : ((4785977640131/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT202 (i+1))
      = (∑ i ∈ Finset.range 328, stT202 (i+1)) + stT202 329 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 328
    simpa using h
  have hprev := st202_p328
  have hstep := st202_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p330 : ((4723411507457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT202 (i+1))
      = (∑ i ∈ Finset.range 329, stT202 (i+1)) + stT202 330 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 329
    simpa using h
  have hprev := st202_p329
  have hstep := st202_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p331 : ((4518666882457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT202 (i+1))
      = (∑ i ∈ Finset.range 330, stT202 (i+1)) + stT202 331 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 330
    simpa using h
  have hprev := st202_p330
  have hstep := st202_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p332 : ((4246248106317/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT202 (i+1))
      = (∑ i ∈ Finset.range 331, stT202 (i+1)) + stT202 332 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 331
    simpa using h
  have hprev := st202_p331
  have hstep := st202_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p333 : ((1001007673083/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT202 (i+1))
      = (∑ i ∈ Finset.range 332, stT202 (i+1)) + stT202 333 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 332
    simpa using h
  have hprev := st202_p332
  have hstep := st202_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p334 : ((24237670479/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT202 (i+1))
      = (∑ i ∈ Finset.range 333, stT202 (i+1)) + stT202 334 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 333
    simpa using h
  have hprev := st202_p333
  have hstep := st202_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p335 : ((3912161812227/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT202 (i+1))
      = (∑ i ∈ Finset.range 334, stT202 (i+1)) + stT202 335 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 334
    simpa using h
  have hprev := st202_p334
  have hstep := st202_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p336 : ((818704982907/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT202 (i+1))
      = (∑ i ∈ Finset.range 335, stT202 (i+1)) + stT202 336 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 335
    simpa using h
  have hprev := st202_p335
  have hstep := st202_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p337 : ((68091734043/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT202 (i+1))
      = (∑ i ∈ Finset.range 336, stT202 (i+1)) + stT202 337 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 336
    simpa using h
  have hprev := st202_p336
  have hstep := st202_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p338 : ((1153205839647/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT202 (i+1))
      = (∑ i ∈ Finset.range 337, stT202 (i+1)) + stT202 338 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 337
    simpa using h
  have hprev := st202_p337
  have hstep := st202_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p339 : ((9540576119051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT202 (i+1))
      = (∑ i ∈ Finset.range 338, stT202 (i+1)) + stT202 339 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 338
    simpa using h
  have hprev := st202_p338
  have hstep := st202_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p340 : ((1910670555457/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT202 (i+1))
      = (∑ i ∈ Finset.range 339, stT202 (i+1)) + stT202 340 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 339
    simpa using h
  have hprev := st202_p339
  have hstep := st202_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p341 : ((9261270451001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT202 (i+1))
      = (∑ i ∈ Finset.range 340, stT202 (i+1)) + stT202 341 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 340
    simpa using h
  have hprev := st202_p340
  have hstep := st202_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p342 : ((1095655847641/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT202 (i+1))
      = (∑ i ∈ Finset.range 341, stT202 (i+1)) + stT202 342 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 341
    simpa using h
  have hprev := st202_p341
  have hstep := st202_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p343 : ((1029250636841/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT202 (i+1))
      = (∑ i ∈ Finset.range 342, stT202 (i+1)) + stT202 343 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 342
    simpa using h
  have hprev := st202_p342
  have hstep := st202_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p344 : ((1961556486289/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT202 (i+1))
      = (∑ i ∈ Finset.range 343, stT202 (i+1)) + stT202 344 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 343
    simpa using h
  have hprev := st202_p343
  have hstep := st202_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p345 : ((3865340546113/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT202 (i+1))
      = (∑ i ∈ Finset.range 344, stT202 (i+1)) + stT202 345 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 344
    simpa using h
  have hprev := st202_p344
  have hstep := st202_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p346 : ((7924258492451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT202 (i+1))
      = (∑ i ∈ Finset.range 345, stT202 (i+1)) + stT202 346 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 345
    simpa using h
  have hprev := st202_p345
  have hstep := st202_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p347 : ((8361324524243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT202 (i+1))
      = (∑ i ∈ Finset.range 346, stT202 (i+1)) + stT202 347 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 346
    simpa using h
  have hprev := st202_p346
  have hstep := st202_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p348 : ((8896964008731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT202 (i+1))
      = (∑ i ∈ Finset.range 347, stT202 (i+1)) + stT202 348 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 347
    simpa using h
  have hprev := st202_p347
  have hstep := st202_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p349 : ((9355640733291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT202 (i+1))
      = (∑ i ∈ Finset.range 348, stT202 (i+1)) + stT202 349 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 348
    simpa using h
  have hprev := st202_p348
  have hstep := st202_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p350 : ((9588748450101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT202 (i+1))
      = (∑ i ∈ Finset.range 349, stT202 (i+1)) + stT202 350 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 349
    simpa using h
  have hprev := st202_p349
  have hstep := st202_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p351 : ((2380543243583/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT202 (i+1))
      = (∑ i ∈ Finset.range 350, stT202 (i+1)) + stT202 351 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 350
    simpa using h
  have hprev := st202_p350
  have hstep := st202_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p352 : ((1147363761537/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT202 (i+1))
      = (∑ i ∈ Finset.range 351, stT202 (i+1)) + stT202 352 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 351
    simpa using h
  have hprev := st202_p351
  have hstep := st202_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p353 : ((2167526344791/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT202 (i+1))
      = (∑ i ∈ Finset.range 352, stT202 (i+1)) + stT202 353 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 352
    simpa using h
  have hprev := st202_p352
  have hstep := st202_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p354 : ((8158319808249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT202 (i+1))
      = (∑ i ∈ Finset.range 353, stT202 (i+1)) + stT202 354 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 353
    simpa using h
  have hprev := st202_p353
  have hstep := st202_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p355 : ((7805295832989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT202 (i+1))
      = (∑ i ∈ Finset.range 354, stT202 (i+1)) + stT202 355 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 354
    simpa using h
  have hprev := st202_p354
  have hstep := st202_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p356 : ((1930286310441/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT202 (i+1))
      = (∑ i ∈ Finset.range 355, stT202 (i+1)) + stT202 356 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 355
    simpa using h
  have hprev := st202_p355
  have hstep := st202_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p357 : ((1982682654441/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT202 (i+1))
      = (∑ i ∈ Finset.range 356, stT202 (i+1)) + stT202 357 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 356
    simpa using h
  have hprev := st202_p356
  have hstep := st202_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p358 : ((32684919027/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT202 (i+1))
      = (∑ i ∈ Finset.range 357, stT202 (i+1)) + stT202 358 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 357
    simpa using h
  have hprev := st202_p357
  have hstep := st202_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p359 : ((4447383385049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT202 (i+1))
      = (∑ i ∈ Finset.range 358, stT202 (i+1)) + stT202 359 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 358
    simpa using h
  have hprev := st202_p358
  have hstep := st202_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p360 : ((18262357199/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT202 (i+1))
      = (∑ i ∈ Finset.range 359, stT202 (i+1)) + stT202 360 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 359
    simpa using h
  have hprev := st202_p359
  have hstep := st202_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p361 : ((4797523785719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT202 (i+1))
      = (∑ i ∈ Finset.range 360, stT202 (i+1)) + stT202 361 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 360
    simpa using h
  have hprev := st202_p360
  have hstep := st202_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p362 : ((9555567953703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT202 (i+1))
      = (∑ i ∈ Finset.range 361, stT202 (i+1)) + stT202 362 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 361
    simpa using h
  have hprev := st202_p361
  have hstep := st202_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p363 : ((9245315594663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT202 (i+1))
      = (∑ i ∈ Finset.range 362, stT202 (i+1)) + stT202 363 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 362
    simpa using h
  have hprev := st202_p362
  have hstep := st202_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p364 : ((8759067085277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT202 (i+1))
      = (∑ i ∈ Finset.range 363, stT202 (i+1)) + stT202 364 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 363
    simpa using h
  have hprev := st202_p363
  have hstep := st202_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p365 : ((8243292403613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT202 (i+1))
      = (∑ i ∈ Finset.range 364, stT202 (i+1)) + stT202 365 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 364
    simpa using h
  have hprev := st202_p364
  have hstep := st202_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p366 : ((981465014353/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT202 (i+1))
      = (∑ i ∈ Finset.range 365, stT202 (i+1)) + stT202 366 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 365
    simpa using h
  have hprev := st202_p365
  have hstep := st202_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p367 : ((1924919454477/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT202 (i+1))
      = (∑ i ∈ Finset.range 366, stT202 (i+1)) + stT202 367 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 366
    simpa using h
  have hprev := st202_p366
  have hstep := st202_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p368 : ((195767993379/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT202 (i+1))
      = (∑ i ∈ Finset.range 367, stT202 (i+1)) + stT202 368 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 367
    simpa using h
  have hprev := st202_p367
  have hstep := st202_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p369 : ((1640995398547/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT202 (i+1))
      = (∑ i ∈ Finset.range 368, stT202 (i+1)) + stT202 369 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 368
    simpa using h
  have hprev := st202_p368
  have hstep := st202_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p370 : ((1742418644097/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT202 (i+1))
      = (∑ i ∈ Finset.range 369, stT202 (i+1)) + stT202 370 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 369
    simpa using h
  have hprev := st202_p369
  have hstep := st202_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p371 : ((9204324166581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT202 (i+1))
      = (∑ i ∈ Finset.range 370, stT202 (i+1)) + stT202 371 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 370
    simpa using h
  have hprev := st202_p370
  have hstep := st202_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p372 : ((2384936725389/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT202 (i+1))
      = (∑ i ∈ Finset.range 371, stT202 (i+1)) + stT202 372 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 371
    simpa using h
  have hprev := st202_p371
  have hstep := st202_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p373 : ((1202862343137/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT202 (i+1))
      = (∑ i ∈ Finset.range 372, stT202 (i+1)) + stT202 373 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 372
    simpa using h
  have hprev := st202_p372
  have hstep := st202_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p374 : ((1178915933221/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT202 (i+1))
      = (∑ i ∈ Finset.range 373, stT202 (i+1)) + stT202 374 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 373
    simpa using h
  have hprev := st202_p373
  have hstep := st202_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p375 : ((4510403532053/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT202 (i+1))
      = (∑ i ∈ Finset.range 374, stT202 (i+1)) + stT202 375 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 374
    simpa using h
  have hprev := st202_p374
  have hstep := st202_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p376 : ((2127104052881/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT202 (i+1))
      = (∑ i ∈ Finset.range 375, stT202 (i+1)) + stT202 376 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 375
    simpa using h
  have hprev := st202_p375
  have hstep := st202_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p377 : ((803865905477/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT202 (i+1))
      = (∑ i ∈ Finset.range 376, stT202 (i+1)) + stT202 377 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 376
    simpa using h
  have hprev := st202_p376
  have hstep := st202_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p378 : ((1548529981371/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT202 (i+1))
      = (∑ i ∈ Finset.range 377, stT202 (i+1)) + stT202 378 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 377
    simpa using h
  have hprev := st202_p377
  have hstep := st202_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p379 : ((1540370396961/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT202 (i+1))
      = (∑ i ∈ Finset.range 378, stT202 (i+1)) + stT202 379 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 378
    simpa using h
  have hprev := st202_p378
  have hstep := st202_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p380 : ((792625645791/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT202 (i+1))
      = (∑ i ∈ Finset.range 379, stT202 (i+1)) + stT202 380 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 379
    simpa using h
  have hprev := st202_p379
  have hstep := st202_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p381 : ((167055132923/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT202 (i+1))
      = (∑ i ∈ Finset.range 380, stT202 (i+1)) + stT202 381 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 380
    simpa using h
  have hprev := st202_p380
  have hstep := st202_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p382 : ((4431763123277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT202 (i+1))
      = (∑ i ∈ Finset.range 381, stT202 (i+1)) + stT202 382 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 381
    simpa using h
  have hprev := st202_p381
  have hstep := st202_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p383 : ((4659479577677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT202 (i+1))
      = (∑ i ∈ Finset.range 382, stT202 (i+1)) + stT202 383 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 382
    simpa using h
  have hprev := st202_p382
  have hstep := st202_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p384 : ((4797924639437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT202 (i+1))
      = (∑ i ∈ Finset.range 383, stT202 (i+1)) + stT202 384 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 383
    simpa using h
  have hprev := st202_p383
  have hstep := st202_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p385 : ((962038776263/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT202 (i+1))
      = (∑ i ∈ Finset.range 384, stT202 (i+1)) + stT202 385 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 384
    simpa using h
  have hprev := st202_p384
  have hstep := st202_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p386 : ((1173404256449/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT202 (i+1))
      = (∑ i ∈ Finset.range 385, stT202 (i+1)) + stT202 386 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 385
    simpa using h
  have hprev := st202_p385
  have hstep := st202_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p387 : ((895990321111/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT202 (i+1))
      = (∑ i ∈ Finset.range 386, stT202 (i+1)) + stT202 387 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 386
    simpa using h
  have hprev := st202_p386
  have hstep := st202_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p388 : ((422643317099/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT202 (i+1))
      = (∑ i ∈ Finset.range 387, stT202 (i+1)) + stT202 388 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 387
    simpa using h
  have hprev := st202_p387
  have hstep := st202_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p389 : ((1600107032429/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT202 (i+1))
      = (∑ i ∈ Finset.range 388, stT202 (i+1)) + stT202 389 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 388
    simpa using h
  have hprev := st202_p388
  have hstep := st202_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p390 : ((308864029651/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT202 (i+1))
      = (∑ i ∈ Finset.range 389, stT202 (i+1)) + stT202 390 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 389
    simpa using h
  have hprev := st202_p389
  have hstep := st202_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p391 : ((7688200837507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT202 (i+1))
      = (∑ i ∈ Finset.range 390, stT202 (i+1)) + stT202 391 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 390
    simpa using h
  have hprev := st202_p390
  have hstep := st202_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p392 : ((7907833136107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT202 (i+1))
      = (∑ i ∈ Finset.range 391, stT202 (i+1)) + stT202 392 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 391
    simpa using h
  have hprev := st202_p391
  have hstep := st202_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p393 : ((416117825131/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT202 (i+1))
      = (∑ i ∈ Finset.range 392, stT202 (i+1)) + stT202 393 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 392
    simpa using h
  have hprev := st202_p392
  have hstep := st202_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p394 : ((2205988118323/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT202 (i+1))
      = (∑ i ∈ Finset.range 393, stT202 (i+1)) + stT202 394 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 393
    simpa using h
  have hprev := st202_p393
  have hstep := st202_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p395 : ((232088107003/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT202 (i+1))
      = (∑ i ∈ Finset.range 394, stT202 (i+1)) + stT202 395 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 394
    simpa using h
  have hprev := st202_p394
  have hstep := st202_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p396 : ((299498614733/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT202 (i+1))
      = (∑ i ∈ Finset.range 395, stT202 (i+1)) + stT202 396 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 395
    simpa using h
  have hprev := st202_p395
  have hstep := st202_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p397 : ((9649707123421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT202 (i+1))
      = (∑ i ∈ Finset.range 396, stT202 (i+1)) + stT202 397 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 396
    simpa using h
  have hprev := st202_p396
  have hstep := st202_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p398 : ((1183158479987/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT202 (i+1))
      = (∑ i ∈ Finset.range 397, stT202 (i+1)) + stT202 398 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 397
    simpa using h
  have hprev := st202_p397
  have hstep := st202_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p399 : ((567389193667/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT202 (i+1))
      = (∑ i ∈ Finset.range 398, stT202 (i+1)) + stT202 399 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 398
    simpa using h
  have hprev := st202_p398
  have hstep := st202_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p400 : ((8586415615051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT202 (i+1))
      = (∑ i ∈ Finset.range 399, stT202 (i+1)) + stT202 400 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 399
    simpa using h
  have hprev := st202_p399
  have hstep := st202_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p401 : ((405640747883/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT202 (i+1))
      = (∑ i ∈ Finset.range 400, stT202 (i+1)) + stT202 401 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 400
    simpa using h
  have hprev := st202_p400
  have hstep := st202_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p402 : ((155494158913/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT202 (i+1))
      = (∑ i ∈ Finset.range 401, stT202 (i+1)) + stT202 402 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 401
    simpa using h
  have hprev := st202_p401
  have hstep := st202_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p403 : ((765483898929/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT202 (i+1))
      = (∑ i ∈ Finset.range 402, stT202 (i+1)) + stT202 403 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 402
    simpa using h
  have hprev := st202_p402
  have hstep := st202_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p404 : ((486349073901/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT202 (i+1))
      = (∑ i ∈ Finset.range 403, stT202 (i+1)) + stT202 404 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 403
    simpa using h
  have hprev := st202_p403
  have hstep := st202_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p405 : ((8122816919867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT202 (i+1))
      = (∑ i ∈ Finset.range 404, stT202 (i+1)) + stT202 405 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 404
    simpa using h
  have hprev := st202_p404
  have hstep := st202_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p406 : ((4297284901977/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT202 (i+1))
      = (∑ i ∈ Finset.range 405, stT202 (i+1)) + stT202 406 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 405
    simpa using h
  have hprev := st202_p405
  have hstep := st202_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p407 : ((9082101312633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT202 (i+1))
      = (∑ i ∈ Finset.range 406, stT202 (i+1)) + stT202 407 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 406
    simpa using h
  have hprev := st202_p406
  have hstep := st202_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p408 : ((9467959228541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT202 (i+1))
      = (∑ i ∈ Finset.range 407, stT202 (i+1)) + stT202 408 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 407
    simpa using h
  have hprev := st202_p407
  have hstep := st202_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p409 : ((9660163390353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT202 (i+1))
      = (∑ i ∈ Finset.range 408, stT202 (i+1)) + stT202 409 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 408
    simpa using h
  have hprev := st202_p408
  have hstep := st202_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p410 : ((4806892017169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT202 (i+1))
      = (∑ i ∈ Finset.range 409, stT202 (i+1)) + stT202 410 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 409
    simpa using h
  have hprev := st202_p409
  have hstep := st202_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p411 : ((4670465060049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT202 (i+1))
      = (∑ i ∈ Finset.range 410, stT202 (i+1)) + stT202 411 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 410
    simpa using h
  have hprev := st202_p410
  have hstep := st202_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p412 : ((8907100652393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT202 (i+1))
      = (∑ i ∈ Finset.range 411, stT202 (i+1)) + stT202 412 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 411
    simpa using h
  have hprev := st202_p411
  have hstep := st202_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p413 : ((1683002495521/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT202 (i+1))
      = (∑ i ∈ Finset.range 412, stT202 (i+1)) + stT202 413 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 412
    simpa using h
  have hprev := st202_p412
  have hstep := st202_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p414 : ((7980051598443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT202 (i+1))
      = (∑ i ∈ Finset.range 413, stT202 (i+1)) + stT202 414 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 413
    simpa using h
  have hprev := st202_p413
  have hstep := st202_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p415 : ((3851615765259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT202 (i+1))
      = (∑ i ∈ Finset.range 414, stT202 (i+1)) + stT202 415 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 414
    simpa using h
  have hprev := st202_p414
  have hstep := st202_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p416 : ((7647962496961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT202 (i+1))
      = (∑ i ∈ Finset.range 415, stT202 (i+1)) + stT202 416 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 415
    simpa using h
  have hprev := st202_p415
  have hstep := st202_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p417 : ((7825973581279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT202 (i+1))
      = (∑ i ∈ Finset.range 416, stT202 (i+1)) + stT202 417 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 416
    simpa using h
  have hprev := st202_p416
  have hstep := st202_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p418 : ((4097657294597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT202 (i+1))
      = (∑ i ∈ Finset.range 417, stT202 (i+1)) + stT202 418 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 417
    simpa using h
  have hprev := st202_p417
  have hstep := st202_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p419 : ((4335354983833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT202 (i+1))
      = (∑ i ∈ Finset.range 418, stT202 (i+1)) + stT202 419 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 418
    simpa using h
  have hprev := st202_p418
  have hstep := st202_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p420 : ((1142943458527/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT202 (i+1))
      = (∑ i ∈ Finset.range 419, stT202 (i+1)) + stT202 420 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 419
    simpa using h
  have hprev := st202_p419
  have hstep := st202_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p421 : ((4753397869363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT202 (i+1))
      = (∑ i ∈ Finset.range 420, stT202 (i+1)) + stT202 421 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 420
    simpa using h
  have hprev := st202_p420
  have hstep := st202_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p422 : ((4839548857147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT202 (i+1))
      = (∑ i ∈ Finset.range 421, stT202 (i+1)) + stT202 422 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 421
    simpa using h
  have hprev := st202_p421
  have hstep := st202_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p423 : ((9622680497133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT202 (i+1))
      = (∑ i ∈ Finset.range 422, stT202 (i+1)) + stT202 423 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 422
    simpa using h
  have hprev := st202_p422
  have hstep := st202_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p424 : ((4675581418953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT202 (i+1))
      = (∑ i ∈ Finset.range 423, stT202 (i+1)) + stT202 424 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 423
    simpa using h
  have hprev := st202_p423
  have hstep := st202_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p425 : ((892584782773/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT202 (i+1))
      = (∑ i ∈ Finset.range 424, stT202 (i+1)) + stT202 425 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 424
    simpa using h
  have hprev := st202_p424
  have hstep := st202_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p426 : ((4220748980679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT202 (i+1))
      = (∑ i ∈ Finset.range 425, stT202 (i+1)) + stT202 426 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 425
    simpa using h
  have hprev := st202_p425
  have hstep := st202_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p427 : ((4002507328963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT202 (i+1))
      = (∑ i ∈ Finset.range 426, stT202 (i+1)) + stT202 427 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 426
    simpa using h
  have hprev := st202_p426
  have hstep := st202_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p428 : ((1927957281113/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT202 (i+1))
      = (∑ i ∈ Finset.range 427, stT202 (i+1)) + stT202 428 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 427
    simpa using h
  have hprev := st202_p427
  have hstep := st202_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p429 : ((7625264601977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT202 (i+1))
      = (∑ i ∈ Finset.range 428, stT202 (i+1)) + stT202 429 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 428
    simpa using h
  have hprev := st202_p428
  have hstep := st202_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p430 : ((7763183885009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT202 (i+1))
      = (∑ i ∈ Finset.range 429, stT202 (i+1)) + stT202 430 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 429
    simpa using h
  have hprev := st202_p429
  have hstep := st202_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p431 : ((8094758084987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT202 (i+1))
      = (∑ i ∈ Finset.range 430, stT202 (i+1)) + stT202 431 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 430
    simpa using h
  have hprev := st202_p430
  have hstep := st202_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p432 : ((8547775762487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT202 (i+1))
      = (∑ i ∈ Finset.range 431, stT202 (i+1)) + stT202 432 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 431
    simpa using h
  have hprev := st202_p431
  have hstep := st202_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p433 : ((9024648225739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT202 (i+1))
      = (∑ i ∈ Finset.range 432, stT202 (i+1)) + stT202 433 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 432
    simpa using h
  have hprev := st202_p432
  have hstep := st202_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p434 : ((4711786905887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT202 (i+1))
      = (∑ i ∈ Finset.range 433, stT202 (i+1)) + stT202 434 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 433
    simpa using h
  have hprev := st202_p433
  have hstep := st202_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p435 : ((4830103990397/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT202 (i+1))
      = (∑ i ∈ Finset.range 434, stT202 (i+1)) + stT202 435 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 434
    simpa using h
  have hprev := st202_p434
  have hstep := st202_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p436 : ((1937051696617/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT202 (i+1))
      = (∑ i ∈ Finset.range 435, stT202 (i+1)) + stT202 436 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 435
    simpa using h
  have hprev := st202_p435
  have hstep := st202_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p437 : ((23735966357/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT202 (i+1))
      = (∑ i ∈ Finset.range 436, stT202 (i+1)) + stT202 437 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 436
    simpa using h
  have hprev := st202_p436
  have hstep := st202_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p438 : ((9128501899559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT202 (i+1))
      = (∑ i ∈ Finset.range 437, stT202 (i+1)) + stT202 438 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 437
    simpa using h
  have hprev := st202_p437
  have hstep := st202_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p439 : ((1732932059803/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT202 (i+1))
      = (∑ i ∈ Finset.range 438, stT202 (i+1)) + stT202 439 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 438
    simpa using h
  have hprev := st202_p438
  have hstep := st202_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p440 : ((1639912111963/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT202 (i+1))
      = (∑ i ∈ Finset.range 439, stT202 (i+1)) + stT202 440 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 439
    simpa using h
  have hprev := st202_p439
  have hstep := st202_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p441 : ((244665882743/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT202 (i+1))
      = (∑ i ∈ Finset.range 440, stT202 (i+1)) + stT202 441 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 440
    simpa using h
  have hprev := st202_p440
  have hstep := st202_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p442 : ((381482594691/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT202 (i+1))
      = (∑ i ∈ Finset.range 441, stT202 (i+1)) + stT202 442 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 441
    simpa using h
  have hprev := st202_p441
  have hstep := st202_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p443 : ((3820367914163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT202 (i+1))
      = (∑ i ∈ Finset.range 442, stT202 (i+1)) + stT202 443 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 442
    simpa using h
  have hprev := st202_p442
  have hstep := st202_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p444 : ((3929689329353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT202 (i+1))
      = (∑ i ∈ Finset.range 443, stT202 (i+1)) + stT202 444 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 443
    simpa using h
  have hprev := st202_p443
  have hstep := st202_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p445 : ((8240289459691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT202 (i+1))
      = (∑ i ∈ Finset.range 444, stT202 (i+1)) + stT202 445 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 444
    simpa using h
  have hprev := st202_p444
  have hstep := st202_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p446 : ((8705779255419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT202 (i+1))
      = (∑ i ∈ Finset.range 445, stT202 (i+1)) + stT202 446 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 445
    simpa using h
  have hprev := st202_p445
  have hstep := st202_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p447 : ((458090692779/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT202 (i+1))
      = (∑ i ∈ Finset.range 446, stT202 (i+1)) + stT202 447 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 446
    simpa using h
  have hprev := st202_p446
  have hstep := st202_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p448 : ((929401161/976562500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT202 (i+1))
      = (∑ i ∈ Finset.range 447, stT202 (i+1)) + stT202 448 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 447
    simpa using h
  have hprev := st202_p447
  have hstep := st202_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p449 : ((9701119726711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT202 (i+1))
      = (∑ i ∈ Finset.range 448, stT202 (i+1)) + stT202 449 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 448
    simpa using h
  have hprev := st202_p448
  have hstep := st202_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p450 : ((2419536451009/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT202 (i+1))
      = (∑ i ∈ Finset.range 449, stT202 (i+1)) + stT202 450 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 449
    simpa using h
  have hprev := st202_p449
  have hstep := st202_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p451 : ((2363391777503/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT202 (i+1))
      = (∑ i ∈ Finset.range 450, stT202 (i+1)) + stT202 451 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 450
    simpa using h
  have hprev := st202_p450
  have hstep := st202_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p452 : ((4536228554881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT202 (i+1))
      = (∑ i ∈ Finset.range 451, stT202 (i+1)) + stT202 452 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 451
    simpa using h
  have hprev := st202_p451
  have hstep := st202_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p453 : ((8610173502247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT202 (i+1))
      = (∑ i ∈ Finset.range 452, stT202 (i+1)) + stT202 453 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 452
    simpa using h
  have hprev := st202_p452
  have hstep := st202_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p454 : ((8157273964951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT202 (i+1))
      = (∑ i ∈ Finset.range 453, stT202 (i+1)) + stT202 454 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 453
    simpa using h
  have hprev := st202_p453
  have hstep := st202_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p455 : ((7801720601591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT202 (i+1))
      = (∑ i ∈ Finset.range 454, stT202 (i+1)) + stT202 455 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 454
    simpa using h
  have hprev := st202_p454
  have hstep := st202_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p456 : ((7611884921837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT202 (i+1))
      = (∑ i ∈ Finset.range 455, stT202 (i+1)) + stT202 456 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 455
    simpa using h
  have hprev := st202_p455
  have hstep := st202_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p457 : ((7623621989817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT202 (i+1))
      = (∑ i ∈ Finset.range 456, stT202 (i+1)) + stT202 457 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 456
    simpa using h
  have hprev := st202_p456
  have hstep := st202_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p458 : ((3916915913789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT202 (i+1))
      = (∑ i ∈ Finset.range 457, stT202 (i+1)) + stT202 458 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 457
    simpa using h
  have hprev := st202_p457
  have hstep := st202_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p459 : ((4100764976249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT202 (i+1))
      = (∑ i ∈ Finset.range 458, stT202 (i+1)) + stT202 459 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 458
    simpa using h
  have hprev := st202_p458
  have hstep := st202_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p460 : ((4328057930603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT202 (i+1))
      = (∑ i ∈ Finset.range 459, stT202 (i+1)) + stT202 460 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 459
    simpa using h
  have hprev := st202_p459
  have hstep := st202_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p461 : ((2277785912127/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT202 (i+1))
      = (∑ i ∈ Finset.range 460, stT202 (i+1)) + stT202 461 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 460
    simpa using h
  have hprev := st202_p460
  have hstep := st202_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p462 : ((4740406190087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT202 (i+1))
      = (∑ i ∈ Finset.range 461, stT202 (i+1)) + stT202 462 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 461
    simpa using h
  have hprev := st202_p461
  have hstep := st202_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p463 : ((9696064148587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT202 (i+1))
      = (∑ i ∈ Finset.range 462, stT202 (i+1)) + stT202 463 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 462
    simpa using h
  have hprev := st202_p462
  have hstep := st202_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p464 : ((1943459771789/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT202 (i+1))
      = (∑ i ∈ Finset.range 463, stT202 (i+1)) + stT202 464 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 463
    simpa using h
  have hprev := st202_p463
  have hstep := st202_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p465 : ((9541362774691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT202 (i+1))
      = (∑ i ∈ Finset.range 464, stT202 (i+1)) + stT202 465 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 464
    simpa using h
  have hprev := st202_p464
  have hstep := st202_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p466 : ((9201690578191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT202 (i+1))
      = (∑ i ∈ Finset.range 465, stT202 (i+1)) + stT202 466 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 465
    simpa using h
  have hprev := st202_p465
  have hstep := st202_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p467 : ((8761658953771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT202 (i+1))
      = (∑ i ∈ Finset.range 466, stT202 (i+1)) + stT202 467 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 466
    simpa using h
  have hprev := st202_p466
  have hstep := st202_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p468 : ((8302561430093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT202 (i+1))
      = (∑ i ∈ Finset.range 467, stT202 (i+1)) + stT202 468 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 467
    simpa using h
  have hprev := st202_p467
  have hstep := st202_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p469 : ((63268084351/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT202 (i+1))
      = (∑ i ∈ Finset.range 468, stT202 (i+1)) + stT202 469 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 468
    simpa using h
  have hprev := st202_p468
  have hstep := st202_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p470 : ((7651059077369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT202 (i+1))
      = (∑ i ∈ Finset.range 469, stT202 (i+1)) + stT202 470 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 469
    simpa using h
  have hprev := st202_p469
  have hstep := st202_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p471 : ((7576374199409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT202 (i+1))
      = (∑ i ∈ Finset.range 470, stT202 (i+1)) + stT202 471 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 470
    simpa using h
  have hprev := st202_p470
  have hstep := st202_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p472 : ((962150229793/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT202 (i+1))
      = (∑ i ∈ Finset.range 471, stT202 (i+1)) + stT202 472 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 471
    simpa using h
  have hprev := st202_p471
  have hstep := st202_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p473 : ((998873191343/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT202 (i+1))
      = (∑ i ∈ Finset.range 472, stT202 (i+1)) + stT202 473 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 472
    simpa using h
  have hprev := st202_p472
  have hstep := st202_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p474 : ((4202176707017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT202 (i+1))
      = (∑ i ∈ Finset.range 473, stT202 (i+1)) + stT202 474 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 473
    simpa using h
  have hprev := st202_p473
  have hstep := st202_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p475 : ((1772603021079/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT202 (i+1))
      = (∑ i ∈ Finset.range 474, stT202 (i+1)) + stT202 475 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 474
    simpa using h
  have hprev := st202_p474
  have hstep := st202_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p476 : ((9285243454101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT202 (i+1))
      = (∑ i ∈ Finset.range 475, stT202 (i+1)) + stT202 476 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 475
    simpa using h
  have hprev := st202_p475
  have hstep := st202_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p477 : ((9596431608829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT202 (i+1))
      = (∑ i ∈ Finset.range 476, stT202 (i+1)) + stT202 477 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 476
    simpa using h
  have hprev := st202_p476
  have hstep := st202_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p478 : ((2435538364321/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT202 (i+1))
      = (∑ i ∈ Finset.range 477, stT202 (i+1)) + stT202 478 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 477
    simpa using h
  have hprev := st202_p477
  have hstep := st202_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p479 : ((2424374404969/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT202 (i+1))
      = (∑ i ∈ Finset.range 478, stT202 (i+1)) + stT202 479 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 478
    simpa using h
  have hprev := st202_p478
  have hstep := st202_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p480 : ((473551251557/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT202 (i+1))
      = (∑ i ∈ Finset.range 479, stT202 (i+1)) + stT202 480 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 479
    simpa using h
  have hprev := st202_p479
  have hstep := st202_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p481 : ((9102918140659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT202 (i+1))
      = (∑ i ∈ Finset.range 480, stT202 (i+1)) + stT202 481 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 480
    simpa using h
  have hprev := st202_p480
  have hstep := st202_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p482 : ((8657580690739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT202 (i+1))
      = (∑ i ∈ Finset.range 481, stT202 (i+1)) + stT202 482 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 481
    simpa using h
  have hprev := st202_p481
  have hstep := st202_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p483 : ((8212246066171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT202 (i+1))
      = (∑ i ∈ Finset.range 482, stT202 (i+1)) + stT202 483 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 482
    simpa using h
  have hprev := st202_p482
  have hstep := st202_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p484 : ((7843521532793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT202 (i+1))
      = (∑ i ∈ Finset.range 483, stT202 (i+1)) + stT202 484 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 483
    simpa using h
  have hprev := st202_p483
  have hstep := st202_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p485 : ((7614262596263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT202 (i+1))
      = (∑ i ∈ Finset.range 484, stT202 (i+1)) + stT202 485 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 484
    simpa using h
  have hprev := st202_p484
  have hstep := st202_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p486 : ((7563038687013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT202 (i+1))
      = (∑ i ∈ Finset.range 485, stT202 (i+1)) + stT202 486 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 485
    simpa using h
  have hprev := st202_p485
  have hstep := st202_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p487 : ((7697835135223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT202 (i+1))
      = (∑ i ∈ Finset.range 486, stT202 (i+1)) + stT202 487 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 486
    simpa using h
  have hprev := st202_p486
  have hstep := st202_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p488 : ((7995093839449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT202 (i+1))
      = (∑ i ∈ Finset.range 487, stT202 (i+1)) + stT202 488 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 487
    simpa using h
  have hprev := st202_p487
  have hstep := st202_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p489 : ((2101012601191/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT202 (i+1))
      = (∑ i ∈ Finset.range 488, stT202 (i+1)) + stT202 489 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 488
    simpa using h
  have hprev := st202_p488
  have hstep := st202_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p490 : ((8855601471173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT202 (i+1))
      = (∑ i ∈ Finset.range 489, stT202 (i+1)) + stT202 490 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 489
    simpa using h
  have hprev := st202_p489
  have hstep := st202_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p491 : ((9274063808009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT202 (i+1))
      = (∑ i ∈ Finset.range 490, stT202 (i+1)) + stT202 491 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 490
    simpa using h
  have hprev := st202_p490
  have hstep := st202_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p492 : ((9589867164167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT202 (i+1))
      = (∑ i ∈ Finset.range 491, stT202 (i+1)) + stT202 492 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 491
    simpa using h
  have hprev := st202_p491
  have hstep := st202_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p493 : ((304719703757/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT202 (i+1))
      = (∑ i ∈ Finset.range 492, stT202 (i+1)) + stT202 493 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 492
    simpa using h
  have hprev := st202_p492
  have hstep := st202_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p494 : ((4865760726191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT202 (i+1))
      = (∑ i ∈ Finset.range 493, stT202 (i+1)) + stT202 494 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 493
    simpa using h
  have hprev := st202_p493
  have hstep := st202_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p495 : ((4767632191817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT202 (i+1))
      = (∑ i ∈ Finset.range 494, stT202 (i+1)) + stT202 495 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 494
    simpa using h
  have hprev := st202_p494
  have hstep := st202_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p496 : ((2298777671209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT202 (i+1))
      = (∑ i ∈ Finset.range 495, stT202 (i+1)) + stT202 496 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 495
    simpa using h
  have hprev := st202_p495
  have hstep := st202_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p497 : ((109589456503/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT202 (i+1))
      = (∑ i ∈ Finset.range 496, stT202 (i+1)) + stT202 497 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 496
    simpa using h
  have hprev := st202_p496
  have hstep := st202_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p498 : ((8321332230673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT202 (i+1))
      = (∑ i ∈ Finset.range 497, stT202 (i+1)) + stT202 498 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 497
    simpa using h
  have hprev := st202_p497
  have hstep := st202_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p499 : ((7929911350719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT202 (i+1))
      = (∑ i ∈ Finset.range 498, stT202 (i+1)) + stT202 499 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 498
    simpa using h
  have hprev := st202_p498
  have hstep := st202_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_p500 : ((7655827753753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT202 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT202 (i+1))
      = (∑ i ∈ Finset.range 499, stT202 (i+1)) + stT202 500 := by
    have h := Finset.sum_range_succ (fun i => stT202 (i+1)) 499
    simpa using h
  have hprev := st202_p499
  have hstep := st202_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st202_s500 :
    |Real.sin (((202 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((118023/125000 : ℚ) : ℝ))
      - ((-790223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -348503/625000) (δ := 10237/1000000000) (ψ := 118023/125000) 202 200
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 202`** (evaluated boundary). -/
theorem station_202_sign : hardyG ((((202:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 202 500 (by norm_num) (by norm_num)
    ((118023/125000 : ℚ) : ℝ)
  have hchain := st202_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT202 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((202 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((118023/125000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st202_c500
  have hsinb := abs_le.mp st202_s500
  have hbdy_lo : ((143037795953793/1632170000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((202 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((118023/125000 : ℚ) : ℝ))) / 2
          - ((((202:ℕ)):ℝ))
            * Real.sin (((202 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((118023/125000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((202:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((202:ℝ) * Real.log (500:ℝ) - ((118023/125000 : ℚ) : ℝ))) / 2
        - ((202:ℝ)) * Real.sin ((202:ℝ) * Real.log (500:ℝ) - ((118023/125000 : ℚ) : ℝ))
        ≥ ((319842661/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((202:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((319842661/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((319842661/2000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((319842661/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((202:ℕ)):ℝ))+1) * (((((202:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((829884510271/2500000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((7655827753753/10000000000000 : ℚ) : ℝ) + ((143037795953793/1632170000000000 : ℚ) : ℝ)
      - ((829884510271/2500000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((118023/125000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((202:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((118023/125000 : ℚ) : ℝ)
        * (riemannZeta (line ((((202:ℕ)):ℝ)))).re
      - Real.sin ((118023/125000 : ℚ) : ℝ)
        * (riemannZeta (line ((((202:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((202:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((202:ℕ)):ℝ))
      = (((((202:ℕ)):ℝ)) * (Real.log ((((202:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((202:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_202
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
  have hθwin : |(((118023/125000 : ℚ) : ℝ) + ((40:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((202:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((202:ℕ)):ℝ)))
    (φ := ((118023/125000 : ℚ) : ℝ) + ((40:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((118023/125000 : ℚ) : ℝ) + ((40:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((118023/125000 : ℚ)) : ℝ) - Real.pi) + ((40:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((118023/125000 : ℚ)) : ℝ) - Real.pi) 40).1,
    (cos_sin_shift ((((118023/125000 : ℚ)) : ℝ) - Real.pi) 40).2]
  exact cos_sin_flip ((118023/125000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_202_sign
end AxiomAudit
