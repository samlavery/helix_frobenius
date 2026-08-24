import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 324` (rung-335.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT324 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((324 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-72323/62500 : ℚ) : ℝ))

theorem st324_c1 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((200967/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72323/250000) (δ := 1/1000000000) (ψ := -72323/62500) 324 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t1 : ((200917/500000 : ℚ) : ℝ) ≤ stT324 1 := by
  have hc : ((200917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200917/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((200917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c2 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((179403/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -572283/5000000) (δ := 813/50000000) (ψ := -72323/62500) 324 36
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t2 : ((1268429211661/2000000000000 : ℚ) : ℝ) ≤ stT324 2 := by
  have hc : ((179383/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1268429211661/2000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((179383/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c3 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((127841/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -323133/1250000) (δ := 4073/250000000) (ψ := -72323/62500) 324 57
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t3 : ((46121620727/156250000000 : ℚ) : ℝ) ≤ stT324 3 := by
  have hc : ((15977/31250 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46121620727/156250000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((15977/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c4 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-481187/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1295503/2500000) (δ := 3257/200000000) (ψ := -72323/62500) 324 72
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t4 : ((-2406435481287/10000000000000 : ℚ) : ℝ) ≤ stT324 4 := by
  have hc : ((-481287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2406435481287/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-481287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c5 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((444049/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 694177/2500000) (δ := 8153/500000000) (ψ := -72323/62500) 324 83
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t5 : ((397079972223/2000000000000 : ℚ) : ℝ) ≤ stT324 5 := by
  have hc : ((443949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((397079972223/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((443949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c6 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-881111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6622509/10000000) (δ := 16369/1000000000) (ψ := -72323/62500) 324 93
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t6 : ((-3597528926913/10000000000000 : ℚ) : ℝ) ≤ stT324 6 := by
  have hc : ((-881211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3597528926913/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-881211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c7 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-123157/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7424149/10000000) (δ := 2047/125000000) (ψ := -72323/62500) 324 101
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t7 : ((-186214793931/500000000000 : ℚ) : ℝ) ≤ stT324 7 := by
  have hc : ((-246339/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-186214793931/500000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-246339/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c8 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-85451/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3244253/5000000) (δ := 1627/100000000) (ψ := -72323/62500) 324 107
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t8 : ((-151075135587/500000000000 : ℚ) : ℝ) ≤ stT324 8 := by
  have hc : ((-85461/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151075135587/500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-85461/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c9 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-996507/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1911239/2500000) (δ := 1629/100000000) (ψ := -72323/62500) 324 113
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t9 : ((-1661011998869/5000000000000 : ℚ) : ℝ) ≤ stT324 9 := by
  have hc : ((-996607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1661011998869/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-996607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c10 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((1751/2000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -630409/5000000) (δ := 4089/250000000) (ψ := -72323/62500) 324 119
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t10 : ((13841286429/50000000000 : ℚ) : ℝ) ≤ stT324 10 := by
  have hc : ((4377/5000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13841286429/50000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((4377/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c11 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((506437/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2599373/10000000) (δ := 16311/1000000000) (ψ := -72323/62500) 324 124
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t11 : ((1526663271081/10000000000000 : ℚ) : ℝ) ≤ stT324 11 := by
  have hc : ((506337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1526663271081/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((506337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c12 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-43353/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 631001/1250000) (δ := 16283/1000000000) (ψ := -72323/62500) 324 128
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t12 : ((-3911819593/31250000000 : ℚ) : ℝ) ≤ stT324 12 := by
  have hc : ((-43363/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3911819593/31250000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-43363/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c13 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-948827/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3525371/5000000) (δ := 8127/500000000) (ψ := -72323/62500) 324 132
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t13 : ((-2631849983427/10000000000000 : ℚ) : ℝ) ≤ stT324 13 := by
  have hc : ((-948927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2631849983427/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-948927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c14 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-31851/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4246369/10000000) (δ := 649/40000000) (ψ := -72323/62500) 324 136
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t14 : ((-21298052997/625000000000 : ℚ) : ℝ) ≤ stT324 14 := by
  have hc : ((-7969/62500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21298052997/625000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-7969/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c15 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((470893/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -540247/2000000) (δ := 16207/1000000000) (ψ := -72323/62500) 324 140
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t15 : ((303895469121/2500000000000 : ℚ) : ℝ) ≤ stT324 15 := by
  have hc : ((470793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((303895469121/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((470793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c16 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((55667/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 122553/500000) (δ := 651/40000000) (ψ := -72323/62500) 324 143
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t16 : ((55657/400000 : ℚ) : ℝ) ≤ stT324 16 := by
  have hc : ((55657/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55657/400000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((55657/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c17 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-100531/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 554137/1250000) (δ := 16353/1000000000) (ψ := -72323/62500) 324 146
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t17 : ((-243944832417/5000000000000 : ℚ) : ℝ) ≤ stT324 17 := by
  have hc : ((-100581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243944832417/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-100581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c18 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((31861/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3607511/10000000) (δ := 16371/1000000000) (ψ := -72323/62500) 324 149
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t18 : ((9379769049/312500000000 : ℚ) : ℝ) ≤ stT324 18 := by
  have hc : ((7959/62500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9379769049/312500000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((7959/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c19 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((993821/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 278053/10000000) (δ := 16293/1000000000) (ψ := -72323/62500) 324 152
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t19 : ((2279751988197/10000000000000 : ℚ) : ℝ) ≤ stT324 19 := by
  have hc : ((993721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2279751988197/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((993721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c20 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-65177/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -662283/1250000) (δ := 8107/500000000) (ψ := -72323/62500) 324 155
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t20 : ((-72884077443/625000000000 : ℚ) : ℝ) ≤ stT324 20 := by
  have hc : ((-130379/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72884077443/625000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-130379/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c21 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((433567/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2805871/10000000) (δ := 8187/500000000) (ψ := -72323/62500) 324 157
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t21 : ((472951075563/5000000000000 : ℚ) : ℝ) ≤ stT324 21 := by
  have hc : ((433467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((472951075563/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((433467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c22 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-220951/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3318409/5000000) (δ := 327/20000000) (ψ := -72323/62500) 324 160
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t22 : ((-3680645311/19531250000 : ℚ) : ℝ) ≤ stT324 22 := by
  have hc : ((-13811/15625 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3680645311/19531250000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-13811/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c23 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((17079/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2046787/10000000) (δ := 8119/500000000) (ψ := -72323/62500) 324 162
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t23 : ((8901740379/62500000000 : ℚ) : ℝ) ≤ stT324 23 := by
  have hc : ((34153/50000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8901740379/62500000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((34153/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c24 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((919407/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1010563/10000000) (δ := 16379/1000000000) (ψ := -72323/62500) 324 164
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t24 : ((1876527139987/10000000000000 : ℚ) : ℝ) ≤ stT324 24 := by
  have hc : ((919307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1876527139987/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((919307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c25 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((485219/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 332557/1250000) (δ := 1621/100000000) (ψ := -72323/62500) 324 166
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t25 : ((485119/5000000 : ℚ) : ℝ) ≤ stT324 25 := by
  have hc : ((485119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((485119/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((485119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c26 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((89349/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 188331/625000) (δ := 3279/200000000) (ψ := -72323/62500) 324 168
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t26 : ((43794686291/625000000000 : ℚ) : ℝ) ≤ stT324 26 := by
  have hc : ((22331/62500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43794686291/625000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((22331/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c27 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((129453/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2167013/10000000) (δ := 8111/500000000) (ψ := -72323/62500) 324 170
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t27 : ((498187617/4000000000 : ℚ) : ℝ) ≤ stT324 27 := by
  have hc : ((129433/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((498187617/4000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((129433/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c28 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((99651/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 208923/10000000) (δ := 16367/1000000000) (ψ := -72323/62500) 324 172
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t28 : ((94151876951/500000000000 : ℚ) : ℝ) ≤ stT324 28 := by
  have hc : ((99641/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94151876951/500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((99641/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c29 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((17671/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55661/200000) (δ := 16251/1000000000) (ψ := -72323/62500) 324 174
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t29 : ((32806788651/400000000000 : ℚ) : ℝ) ≤ stT324 29 := by
  have hc : ((17667/40000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32806788651/400000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((17667/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c30 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-451071/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3369381/5000000) (δ := 8169/500000000) (ψ := -72323/62500) 324 176
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t30 : ((-411815278391/2500000000000 : ℚ) : ℝ) ≤ stT324 30 := by
  have hc : ((-451121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-411815278391/2500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-451121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c31 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-74373/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2056547/5000000) (δ := 16231/1000000000) (ψ := -72323/62500) 324 177
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t31 : ((-66878764771/5000000000000 : ℚ) : ℝ) ≤ stT324 31 := by
  have hc : ((-74473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66878764771/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-74473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c32 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((100667/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -317277/2000000) (δ := 16387/1000000000) (ψ := -72323/62500) 324 179
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t32 : ((177933602847/1250000000000 : ℚ) : ℝ) ≤ stT324 32 := by
  have hc : ((201309/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177933602847/1250000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((201309/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c33 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-249003/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7630647/10000000) (δ := 16309/1000000000) (ψ := -72323/62500) 324 180
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t33 : ((-108375553689/625000000000 : ℚ) : ℝ) ≤ stT324 33 := by
  have hc : ((-62257/62500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108375553689/625000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-62257/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c34 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((987503/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 395651/10000000) (δ := 4077/250000000) (ψ := -72323/62500) 324 182
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t34 : ((338676266791/2000000000000 : ℚ) : ℝ) ≤ stT324 34 := by
  have hc : ((987403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((338676266791/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((987403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c35 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-62009/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7540401/10000000) (δ := 407/25000000) (ψ := -72323/62500) 324 184
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t35 : ((-419299740849/2500000000000 : ℚ) : ℝ) ≤ stT324 35 := by
  have hc : ((-248061/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-419299740849/2500000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-248061/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c36 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((985249/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -85987/2000000) (δ := 1623/100000000) (ψ := -72323/62500) 324 185
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t36 : ((820957171617/5000000000000 : ℚ) : ℝ) ≤ stT324 36 := by
  have hc : ((985149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((820957171617/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((985149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c37 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-752151/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1513823/2500000) (δ := 16337/1000000000) (ψ := -72323/62500) 324 186
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t37 : ((-123669312149/1000000000000 : ℚ) : ℝ) ≤ stT324 37 := by
  have hc : ((-752251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123669312149/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-752251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c38 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((66989/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3759393/10000000) (δ := 4063/250000000) (ψ := -72323/62500) 324 188
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t38 : ((54254136123/5000000000000 : ℚ) : ℝ) ≤ stT324 38 := by
  have hc : ((66889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54254136123/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((66889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c39 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((404273/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1572799/10000000) (δ := 8129/500000000) (ψ := -72323/62500) 324 189
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t39 : ((647274609663/5000000000000 : ℚ) : ℝ) ≤ stT324 39 := by
  have hc : ((404223/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((647274609663/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((404223/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c40 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-2592/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3186127/5000000) (δ := 8183/500000000) (ψ := -72323/62500) 324 190
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t40 : ((-65580902303/500000000000 : ℚ) : ℝ) ≤ stT324 40 := by
  have hc : ((-41477/50000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65580902303/500000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-41477/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c41 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-107901/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5042667/10000000) (δ := 16223/1000000000) (ψ := -72323/62500) 324 192
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t41 : ((-42138033847/625000000000 : ℚ) : ℝ) ≤ stT324 41 := by
  have hc : ((-53963/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42138033847/625000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-53963/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c42 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((220273/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -615787/5000000) (δ := 16287/1000000000) (ψ := -72323/62500) 324 193
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t42 : ((42481241523/312500000000 : ℚ) : ℝ) ≤ stT324 42 := by
  have hc : ((27531/31250 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42481241523/312500000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((27531/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c43 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((330717/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 265021/1250000) (δ := 8197/500000000) (ψ := -72323/62500) 324 194
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t43 : ((100852442999/1000000000000 : ℚ) : ℝ) ≤ stT324 43 := by
  have hc : ((330667/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100852442999/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((330667/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c44 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-214183/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5033699/10000000) (δ := 16301/1000000000) (ψ := -72323/62500) 324 195
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t44 : ((-322968458781/5000000000000 : ℚ) : ℝ) ≤ stT324 44 := by
  have hc : ((-214233/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-322968458781/5000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-214233/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c45 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-991547/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58818/78125) (δ := 16209/1000000000) (ψ := -72323/62500) 324 196
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t45 : ((-184782510333/1250000000000 : ℚ) : ℝ) ≤ stT324 45 := by
  have hc : ((-991647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184782510333/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-991647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c46 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-3039/4000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3042157/5000000) (δ := 819/50000000) (ψ := -72323/62500) 324 198
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t46 : ((-1120338037/10000000000 : ℚ) : ℝ) ≤ stT324 46 := by
  have hc : ((-15197/20000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1120338037/10000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-15197/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c47 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-88567/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2186087/5000000) (δ := 16273/1000000000) (ψ := -72323/62500) 324 199
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t47 : ((-2585223741/100000000000 : ℚ) : ℝ) ≤ stT324 47 := by
  have hc : ((-88617/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2585223741/100000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-88617/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c48 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((70463/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3026883/10000000) (δ := 16237/1000000000) (ψ := -72323/62500) 324 200
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t48 : ((813405321/16000000000 : ℚ) : ℝ) ≤ stT324 48 := by
  have hc : ((70443/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((813405321/16000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((70443/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c49 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((171773/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1016647/5000000) (δ := 3269/200000000) (ψ := -72323/62500) 324 201
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t49 : ((61338553027/625000000000 : ℚ) : ℝ) ≤ stT324 49 := by
  have hc : ((42937/62500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61338553027/625000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((42937/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c50 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((213027/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137699/1000000) (δ := 16351/1000000000) (ψ := -72323/62500) 324 202
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t50 : ((150615098713/1250000000000 : ℚ) : ℝ) ≤ stT324 50 := by
  have hc : ((106501/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150615098713/1250000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((106501/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c51 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((913927/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1044847/10000000) (δ := 4061/250000000) (ψ := -72323/62500) 324 203
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t51 : ((31990341789/250000000000 : ℚ) : ℝ) ≤ stT324 51 := by
  have hc : ((913827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31990341789/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((913827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c52 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((114657/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1024149/10000000) (δ := 8133/500000000) (ψ := -72323/62500) 324 204
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t52 : ((1271866083/10000000000 : ℚ) : ℝ) ≤ stT324 52 := by
  have hc : ((229289/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1271866083/10000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((229289/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c53 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((108401/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -130307/1000000) (δ := 16373/1000000000) (ψ := -72323/62500) 324 205
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t53 : ((59553194217/500000000000 : ℚ) : ℝ) ≤ stT324 53 := by
  have hc : ((216777/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59553194217/500000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((216777/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c54 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((732933/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1870433/10000000) (δ := 16323/1000000000) (ψ := -72323/62500) 324 206
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t54 : ((997258932891/10000000000000 : ℚ) : ℝ) ≤ stT324 54 := by
  have hc : ((732833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((997258932891/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((732833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c55 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((465807/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -869/3200) (δ := 3243/200000000) (ψ := -72323/62500) 324 207
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t55 : ((627958853093/10000000000000 : ℚ) : ℝ) ≤ stT324 55 := by
  have hc : ((465707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((627958853093/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((465707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c56 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((7869/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3828603/10000000) (δ := 3259/200000000) (ψ := -72323/62500) 324 208
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t56 : ((5244332897/1000000000000 : ℚ) : ℝ) ≤ stT324 56 := by
  have hc : ((7849/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5244332897/1000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((7849/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c57 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-121861/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5199891/10000000) (δ := 16401/1000000000) (ψ := -72323/62500) 324 209
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t57 : ((-80721014619/1250000000000 : ℚ) : ℝ) ≤ stT324 57 := by
  have hc : ((-60943/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80721014619/1250000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-60943/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c58 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-915763/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -426281/625000) (δ := 8147/500000000) (ψ := -72323/62500) 324 210
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t58 : ((-240517530019/2000000000000 : ℚ) : ℝ) ≤ stT324 58 := by
  have hc : ((-915863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-240517530019/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-915863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c59 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-945651/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 439123/625000) (δ := 8147/500000000) (ψ := -72323/62500) 324 210
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t59 : ((-123126376939/1000000000000 : ℚ) : ℝ) ≤ stT324 59 := by
  have hc : ((-945751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123126376939/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-945751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c60 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-391173/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1232939/2500000) (δ := 2027/125000000) (ψ := -72323/62500) 324 211
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t60 : ((-101026297327/2000000000000 : ℚ) : ℝ) ≤ stT324 60 := by
  have hc : ((-391273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101026297327/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-391273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c61 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((501893/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1306263/5000000) (δ := 4081/250000000) (ψ := -72323/62500) 324 212
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t61 : ((40154981239/625000000000 : ℚ) : ℝ) ≤ stT324 61 := by
  have hc : ((501793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40154981239/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((501793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c62 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((999543/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75567/10000000) (δ := 4093/250000000) (ψ := -72323/62500) 324 213
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t62 : ((1269293609443/10000000000000 : ℚ) : ℝ) ≤ stT324 62 := by
  have hc : ((999443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1269293609443/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((999443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c63 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((481151/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -334009/1250000) (δ := 3253/200000000) (ψ := -72323/62500) 324 214
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t63 : ((606067014931/10000000000000 : ℚ) : ℝ) ≤ stT324 63 := by
  have hc : ((481051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((606067014931/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((481051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c64 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-125567/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -702989/1250000) (δ := 3249/200000000) (ψ := -72323/62500) 324 215
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t64 : ((-156983875587/2000000000000 : ℚ) : ℝ) ≤ stT324 64 := by
  have hc : ((-125587/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156983875587/2000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-125587/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c65 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-466561/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 693449/1000000) (δ := 3249/200000000) (ψ := -72323/62500) 324 215
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t65 : ((-144690005157/1250000000000 : ℚ) : ℝ) ≤ stT324 65 := by
  have hc : ((-466611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144690005157/1250000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-466611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c66 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((133119/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1796601/5000000) (δ := 511/31250000) (ψ := -72323/62500) 324 216
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t66 : ((81867474683/5000000000000 : ℚ) : ℝ) ≤ stT324 66 := by
  have hc : ((133019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81867474683/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((133019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c67 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((249913/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 65937/10000000) (δ := 2043/125000000) (ψ := -72323/62500) 324 217
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t67 : ((4770104223/39062500000 : ℚ) : ℝ) ≤ stT324 67 := by
  have hc : ((15618/15625 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4770104223/39062500000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((15618/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c68 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((113831/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -728359/2000000) (δ := 4059/250000000) (ψ := -72323/62500) 324 218
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t68 : ((68959540809/5000000000000 : ℚ) : ℝ) ≤ stT324 68 := by
  have hc : ((113731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68959540809/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((113731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c69 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-49567/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -752473/1000000) (δ := 8137/500000000) (ψ := -72323/62500) 324 219
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t69 : ((-14919424587/125000000000 : ℚ) : ℝ) ≤ stT324 69 := by
  have hc : ((-12393/12500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14919424587/125000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-12393/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c70 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-81161/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4130117/10000000) (δ := 8137/500000000) (ψ := -72323/62500) 324 219
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t70 : ((-97125503769/10000000000000 : ℚ) : ℝ) ≤ stT324 70 := by
  have hc : ((-81261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97125503769/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-81261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c71 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((62461/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -138/15625) (δ := 16381/1000000000) (ψ := -72323/62500) 324 220
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t71 : ((296480442639/2500000000000 : ℚ) : ℝ) ≤ stT324 71 := by
  have hc : ((249819/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((296480442639/2500000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((249819/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c72 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-214477/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4467381/10000000) (δ := 3263/200000000) (ψ := -72323/62500) 324 221
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t72 : ((-15805098089/625000000000 : ℚ) : ℝ) ≤ stT324 72 := by
  have hc : ((-214577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15805098089/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-214577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c73 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-896267/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 838149/1250000) (δ := 3263/200000000) (ψ := -72323/62500) 324 221
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t73 : ((-262279673301/2500000000000 : ℚ) : ℝ) ≤ stT324 73 := by
  have hc : ((-896367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-262279673301/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-896367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c74 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((86449/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 403553/2000000) (δ := 1013/62500000) (ψ := -72323/62500) 324 222
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t74 : ((50240178387/625000000000 : ℚ) : ℝ) ≤ stT324 74 := by
  have hc : ((172873/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50240178387/625000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((172873/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c75 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((6709/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2817487/10000000) (δ := 16303/1000000000) (ψ := -72323/62500) 324 223
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t75 : ((1239212493/25000000000 : ℚ) : ℝ) ≤ stT324 75 := by
  have hc : ((107319/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1239212493/25000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((107319/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c76 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-999739/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7796839/10000000) (δ := 16393/1000000000) (ψ := -72323/62500) 324 224
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t76 : ((-1146894320281/10000000000000 : ℚ) : ℝ) ≤ stT324 76 := by
  have hc : ((-999839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1146894320281/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-999839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c77 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((219359/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1395781/5000000) (δ := 16393/1000000000) (ψ := -72323/62500) 324 224
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t77 : ((49985126589/1000000000000 : ℚ) : ℝ) ≤ stT324 77 := by
  have hc : ((219309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49985126589/1000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((219309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c78 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((552147/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2464647/10000000) (δ := 8143/500000000) (ψ := -72323/62500) 324 225
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t78 : ((625070121019/10000000000000 : ℚ) : ℝ) ≤ stT324 78 := by
  have hc : ((552047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((625070121019/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((552047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c79 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-1 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7853943/10000000) (δ := 8143/500000000) (ψ := -72323/62500) 324 225
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t79 : ((-351625159/3125000000 : ℚ) : ℝ) ≤ stT324 79 := by
  have hc : ((-10001/10000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-351625159/3125000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-10001/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c80 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((148671/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 291851/1250000) (δ := 507/31250000) (ψ := -72323/62500) 324 226
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t80 : ((83095566659/1250000000000 : ℚ) : ℝ) ≤ stT324 80 := by
  have hc : ((74323/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83095566659/1250000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((74323/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c81 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((121969/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -331093/1000000) (δ := 16331/1000000000) (ψ := -72323/62500) 324 227
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t81 : ((135465542009/5000000000000 : ℚ) : ℝ) ≤ stT324 81 := by
  have hc : ((121919/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135465542009/5000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((121919/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c82 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-22053/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6627851/10000000) (δ := 16331/1000000000) (ψ := -72323/62500) 324 227
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t82 : ((-12178120769/125000000000 : ℚ) : ℝ) ≤ stT324 82 := by
  have hc : ((-44111/50000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12178120769/125000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-44111/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c83 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((478359/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 738221/10000000) (δ := 3273/200000000) (ψ := -72323/62500) 324 228
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t83 : ((262506023689/2500000000000 : ℚ) : ℝ) ≤ stT324 83 := by
  have hc : ((478309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((262506023689/2500000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((478309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c84 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-127853/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -263453/500000) (δ := 16273/500000000) (ψ := -72323/62500) 324 229
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t84 : ((-6976320351/125000000000 : ℚ) : ℝ) ≤ stT324 84 := by
  have hc : ((-63939/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6976320351/125000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-63939/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c85 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-15531/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1079211/2500000) (δ := 16257/1000000000) (ψ := -72323/62500) 324 229
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t85 : ((-16856592273/1000000000000 : ℚ) : ℝ) ≤ stT324 85 := by
  have hc : ((-15541/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16856592273/1000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-15541/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c86 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((144007/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1917359/10000000) (δ := 16253/1000000000) (ψ := -72323/62500) 324 230
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t86 : ((155265069749/2000000000000 : ℚ) : ℝ) ≤ stT324 86 := by
  have hc : ((143987/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155265069749/2000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((143987/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c87 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-986777/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 744697/1000000) (δ := 16253/1000000000) (ψ := -72323/62500) 324 230
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t87 : ((-1058043661101/10000000000000 : ℚ) : ℝ) ≤ stT324 87 := by
  have hc : ((-986877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1058043661101/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-986877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c88 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((921643/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 498127/5000000) (δ := 409/25000000) (ψ := -72323/62500) 324 231
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t88 : ((982367602629/10000000000000 : ℚ) : ℝ) ≤ stT324 88 := by
  have hc : ((921543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((982367602629/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((921543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c89 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-607453/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1111823/2000000) (δ := 1021/62500000) (ψ := -72323/62500) 324 232
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t89 : ((-322002482447/5000000000000 : ℚ) : ℝ) ≤ stT324 89 := by
  have hc : ((-607553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-322002482447/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-607553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c90 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((43353/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1745629/5000000) (δ := 1021/62500000) (ψ := -72323/62500) 324 232
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t90 : ((178405071/9765625000 : ℚ) : ℝ) ≤ stT324 90 := by
  have hc : ((2708/15625 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178405071/9765625000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((2708/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c91 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((261201/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1633163/5000000) (δ := 16287/500000000) (ψ := -72323/62500) 324 233
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t91 : ((68427000171/2500000000000 : ℚ) : ℝ) ≤ stT324 91 := by
  have hc : ((261101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68427000171/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((261101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c92 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-77003/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1396551/2500000) (δ := 16229/1000000000) (ψ := -72323/62500) 324 233
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t92 : ((-160588561763/2500000000000 : ℚ) : ℝ) ≤ stT324 92 := by
  have hc : ((-154031/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160588561763/2500000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-154031/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c93 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((854623/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -136493/1000000) (δ := 8141/500000000) (ψ := -72323/62500) 324 234
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t93 : ((886098479373/10000000000000 : ℚ) : ℝ) ≤ stT324 93 := by
  have hc : ((854523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((886098479373/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((854523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c94 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-243849/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7298263/10000000) (δ := 8141/500000000) (ψ := -72323/62500) 324 234
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t94 : ((-62884252207/625000000000 : ℚ) : ℝ) ≤ stT324 94 := by
  have hc : ((-121937/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62884252207/625000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-121937/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c95 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((498953/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 161801/10000000) (δ := 16389/1000000000) (ψ := -72323/62500) 324 235
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t95 : ((255931751067/2500000000000 : ℚ) : ℝ) ≤ stT324 95 := by
  have hc : ((498903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((255931751067/2500000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((498903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c96 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-950539/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -706441/1000000) (δ := 16307/1000000000) (ψ := -72323/62500) 324 236
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t96 : ((-970242126819/10000000000000 : ℚ) : ℝ) ≤ stT324 96 := by
  have hc : ((-950639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-970242126819/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-950639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c97 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((53869/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 664729/5000000) (δ := 16307/1000000000) (ψ := -72323/62500) 324 236
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t97 : ((109378655523/1250000000000 : ℚ) : ℝ) ≤ stT324 97 := by
  have hc : ((215451/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109378655523/1250000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((215451/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c98 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-756209/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -303537/500000) (δ := 16203/1000000000) (ψ := -72323/62500) 324 237
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t98 : ((-763987805277/10000000000000 : ℚ) : ℝ) ≤ stT324 98 := by
  have hc : ((-756309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-763987805277/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-756309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c99 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((651617/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16818/78125) (δ := 16203/1000000000) (ψ := -72323/62500) 324 237
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t99 : ((654798691129/10000000000000 : ℚ) : ℝ) ≤ stT324 99 := by
  have hc : ((651517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((654798691129/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((651517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c100 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-560517/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1353629/2500000) (δ := 1631/100000000) (ψ := -72323/62500) 324 238
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t100 : ((-560617/10000000 : ℚ) : ℝ) ≤ stT324 100 := by
  have hc : ((-560617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-560617/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-560617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c101 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((122627/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 661327/2500000) (δ := 1631/100000000) (ψ := -72323/62500) 324 238
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t101 : ((60996763137/1250000000000 : ℚ) : ℝ) ≤ stT324 101 := by
  have hc : ((61301/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60996763137/1250000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((61301/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c102 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-55731/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5082293/10000000) (δ := 8193/500000000) (ψ := -72323/62500) 324 239
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t102 : ((-27597157519/625000000000 : ℚ) : ℝ) ≤ stT324 102 := by
  have hc : ((-111487/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27597157519/625000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-111487/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c103 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((214207/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 705037/2500000) (δ := 8193/500000000) (ψ := -72323/62500) 324 239
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t103 : ((211015102653/5000000000000 : ℚ) : ℝ) ≤ stT324 103 := by
  have hc : ((214157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211015102653/5000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((214157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c104 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-438451/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1265419/2500000) (δ := 8139/500000000) (ψ := -72323/62500) 324 240
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t104 : ((-430034778131/10000000000000 : ℚ) : ℝ) ≤ stT324 104 := by
  have hc : ((-438551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-430034778131/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-438551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c105 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((474987/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2689619/10000000) (δ := 8139/500000000) (ψ := -72323/62500) 324 240
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t105 : ((4634422233/100000000000 : ℚ) : ℝ) ≤ stT324 105 := by
  have hc : ((474887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4634422233/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((474887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c106 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-535789/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5340597/10000000) (δ := 2029/125000000) (ψ := -72323/62500) 324 241
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t106 : ((-260250741627/5000000000000 : ℚ) : ℝ) ≤ stT324 106 := by
  have hc : ((-535889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-260250741627/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-535889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c107 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((308427/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2265141/10000000) (δ := 2029/125000000) (ψ := -72323/62500) 324 241
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t107 : ((18632446717/312500000000 : ℚ) : ℝ) ≤ stT324 107 := by
  have hc : ((308377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18632446717/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((308377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c108 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-712009/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2953939/5000000) (δ := 16339/1000000000) (ψ := -72323/62500) 324 242
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t108 : ((-685227597359/10000000000000 : ℚ) : ℝ) ≤ stT324 108 := by
  have hc : ((-712109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-685227597359/10000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-712109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c109 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((203029/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24337/156250) (δ := 16339/1000000000) (ψ := -72323/62500) 324 242
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t109 : ((24305313663/312500000000 : ℚ) : ℝ) ≤ stT324 109 := by
  have hc : ((50751/62500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24305313663/312500000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((50751/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c110 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-226149/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6753071/10000000) (δ := 16357/1000000000) (ψ := -72323/62500) 324 243
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t110 : ((-107824270281/1250000000000 : ℚ) : ℝ) ≤ stT324 110 := by
  have hc : ((-113087/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107824270281/1250000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-113087/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c111 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((243363/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 144337/2500000) (δ := 16357/1000000000) (ψ := -72323/62500) 324 243
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t111 : ((115482983033/1250000000000 : ℚ) : ℝ) ≤ stT324 111 := by
  have hc : ((121669/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115482983033/1250000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((121669/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c112 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-249997/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3920957/5000000) (δ := 16357/1000000000) (ψ := -72323/62500) 324 243
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t112 : ((-7382774627/78125000000 : ℚ) : ℝ) ≤ stT324 112 := by
  have hc : ((-125011/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7382774627/78125000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-125011/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c113 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((964729/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -665959/10000000) (δ := 13/800000) (ψ := -72323/62500) 324 244
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t113 : ((11343072411/125000000000 : ℚ) : ℝ) ≤ stT324 113 := by
  have hc : ((964629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11343072411/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((964629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c114 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-850773/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6470627/10000000) (δ := 13/800000) (ψ := -72323/62500) 324 244
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t114 : ((-398457869789/5000000000000 : ℚ) : ℝ) ≤ stT324 114 := by
  have hc : ((-850873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-398457869789/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-850873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c115 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((162119/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2163039/10000000) (δ := 813/50000000) (ψ := -72323/62500) 324 245
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t115 : ((9447081461/156250000000 : ℚ) : ℝ) ≤ stT324 115 := by
  have hc : ((81047/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9447081461/156250000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((81047/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c116 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-360851/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4849941/10000000) (δ := 813/50000000) (ψ := -72323/62500) 324 245
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t116 : ((-335134701627/10000000000000 : ℚ) : ℝ) ≤ stT324 116 := by
  have hc : ((-360951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-335134701627/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-360951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c117 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((8739/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -488143/1250000) (δ := 1023/62500000) (ψ := -72323/62500) 324 246
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t117 : ((15973511/20000000000 : ℚ) : ℝ) ≤ stT324 117 := by
  have hc : ((8639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15973511/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((8639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c118 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((366633/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2988523/10000000) (δ := 1023/62500000) (ψ := -72323/62500) 324 246
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t118 : ((168710374971/5000000000000 : ℚ) : ℝ) ≤ stT324 118 := by
  have hc : ((366533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168710374971/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((366533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c119 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-352637/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5884013/10000000) (δ := 2041/125000000) (ψ := -72323/62500) 324 247
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t119 : ((-323307820213/5000000000000 : ℚ) : ℝ) ≤ stT324 119 := by
  have hc : ((-352687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-323307820213/5000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-352687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c120 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((117087/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 89431/1000000) (δ := 2041/125000000) (ψ := -72323/62500) 324 247
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t120 : ((21374759763/250000000000 : ℚ) : ℝ) ≤ stT324 120 := by
  have hc : ((234149/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21374759763/250000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((234149/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c121 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-199097/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3808169/5000000) (δ := 2041/125000000) (ψ := -72323/62500) 324 247
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t121 : ((-181015472647/2000000000000 : ℚ) : ℝ) ≤ stT324 121 := by
  have hc : ((-199117/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181015472647/2000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-199117/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c122 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((420959/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35623/250000) (δ := 16221/1000000000) (ψ := -72323/62500) 324 248
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t122 : ((381072909513/5000000000000 : ℚ) : ℝ) ≤ stT324 122 := by
  have hc : ((420909/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((381072909513/5000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((420909/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c123 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-483059/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5187353/10000000) (δ := 16221/1000000000) (ψ := -72323/62500) 324 248
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t123 : ((-43564997553/1000000000000 : ℚ) : ℝ) ≤ stT324 123 := by
  have hc : ((-483159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43564997553/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-483159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c124 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-6977/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1980939/5000000) (δ := 16289/1000000000) (ψ := -72323/62500) 324 249
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t124 : ((-6310435729/5000000000000 : ℚ) : ℝ) ≤ stT324 124 := by
  have hc : ((-7027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6310435729/5000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-7027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c125 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((26267/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 636051/2500000) (δ := 16289/1000000000) (ψ := -72323/62500) 324 249
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t125 : ((11744720937/250000000000 : ℚ) : ℝ) ≤ stT324 125 := by
  have hc : ((13131/25000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11744720937/250000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((13131/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c126 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-897033/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6709517/10000000) (δ := 4099/250000000) (ψ := -72323/62500) 324 250
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t126 : ((-799229772843/10000000000000 : ℚ) : ℝ) ≤ stT324 126 := by
  have hc : ((-897133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-799229772843/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-897133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c127 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((397/400 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -153193/5000000) (δ := 4099/250000000) (ψ := -72323/62500) 324 250
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t127 : ((550382559/6250000000 : ℚ) : ℝ) ≤ stT324 127 := by
  have hc : ((2481/2500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((550382559/6250000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((2481/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c128 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-749857/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3023303/5000000) (δ := 4099/250000000) (ψ := -72323/62500) 324 250
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t128 : ((-165718748247/2500000000000 : ℚ) : ℝ) ≤ stT324 128 := by
  have hc : ((-749957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165718748247/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-749957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c129 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((56431/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -209861/625000) (δ := 16299/1000000000) (ψ := -72323/62500) 324 251
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t129 : ((496626627/25000000000 : ℚ) : ℝ) ≤ stT324 129 := by
  have hc : ((28203/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((496626627/25000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((28203/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c130 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((400423/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 724261/2500000) (δ := 16299/1000000000) (ψ := -72323/62500) 324 251
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t130 : ((175553244867/5000000000000 : ℚ) : ℝ) ≤ stT324 130 := by
  have hc : ((400323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175553244867/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((400323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c131 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-43879/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -660397/1000000) (δ := 16211/1000000000) (ψ := -72323/62500) 324 252
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t131 : ((-1917083511/25000000000 : ℚ) : ℝ) ≤ stT324 131 := by
  have hc : ((-10971/12500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1917083511/25000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-10971/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c132 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((984253/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -111061/2500000) (δ := 16211/1000000000) (ψ := -72323/62500) 324 252
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t132 : ((214148740341/2500000000000 : ℚ) : ℝ) ≤ stT324 132 := by
  have hc : ((984153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((214148740341/2500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((984153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c133 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-320883/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1417247/2500000) (δ := 16211/1000000000) (ψ := -72323/62500) 324 252
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t133 : ((-27828421363/500000000000 : ℚ) : ℝ) ≤ stT324 133 := by
  have hc : ((-320933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27828421363/500000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-320933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c134 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-8911/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3971549/10000000) (δ := 6497/200000000) (ψ := -72323/62500) 324 253
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t134 : ((-7741130109/5000000000000 : ℚ) : ℝ) ≤ stT324 134 := by
  have hc : ((-8961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7741130109/5000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-8961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c135 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((681999/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2050761/10000000) (δ := 8159/500000000) (ψ := -72323/62500) 324 253
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t135 : ((293442278569/5000000000000 : ℚ) : ℝ) ≤ stT324 135 := by
  have hc : ((681899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((293442278569/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((681899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c136 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-997561/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3839661/5000000) (δ := 8189/500000000) (ψ := -72323/62500) 324 254
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t136 : ((-855487323873/10000000000000 : ℚ) : ℝ) ≤ stT324 136 := by
  have hc : ((-997661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-855487323873/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-997661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c137 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((766083/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1745181/10000000) (δ := 8189/500000000) (ψ := -72323/62500) 324 254
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t137 : ((654422937931/10000000000000 : ℚ) : ℝ) ≤ stT324 137 := by
  have hc : ((765983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((654422937931/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((765983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c138 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-699/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2072853/5000000) (δ := 8189/500000000) (ψ := -72323/62500) 324 254
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t138 : ((-2978548243/400000000000 : ℚ) : ℝ) ≤ stT324 138 := by
  have hc : ((-3499/40000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2978548243/400000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-3499/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c139 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-655413/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2856907/5000000) (δ := 16271/1000000000) (ψ := -72323/62500) 324 255
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t139 : ((-555998915957/10000000000000 : ℚ) : ℝ) ≤ stT324 139 := by
  have hc : ((-655513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-555998915957/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-655513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c140 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((999313/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 92671/10000000) (δ := 16271/1000000000) (ψ := -72323/62500) 324 255
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t140 : ((422244431901/5000000000000 : ℚ) : ℝ) ≤ stT324 140 := by
  have hc : ((999213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((422244431901/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((999213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c141 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-10903/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1171553/2000000) (δ := 16271/1000000000) (ψ := -72323/62500) 324 255
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t141 : ((-18366598237/312500000000 : ℚ) : ℝ) ≤ stT324 141 := by
  have hc : ((-174473/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18366598237/312500000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-174473/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c142 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-39713/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2062883/5000000) (δ := 16239/1000000000) (ψ := -72323/62500) 324 256
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t142 : ((-16684196933/2500000000000 : ℚ) : ℝ) ≤ stT324 142 := by
  have hc : ((-39763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16684196933/2500000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-39763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c143 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((811901/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 155849/1000000) (δ := 16239/1000000000) (ψ := -72323/62500) 324 256
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t143 : ((339431045921/5000000000000 : ℚ) : ℝ) ≤ stT324 143 := by
  have hc : ((811801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((339431045921/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((811801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c144 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-193259/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 450191/625000) (δ := 16239/1000000000) (ψ := -72323/62500) 324 256
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t144 : ((-80532981093/1000000000000 : ℚ) : ℝ) ≤ stT324 144 := by
  have hc : ((-193279/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80532981093/1000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-193279/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c145 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((79919/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1449651/5000000) (δ := 16347/1000000000) (ψ := -72323/62500) 324 257
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t145 : ((33176222073/1000000000000 : ℚ) : ℝ) ≤ stT324 145 := by
  have hc : ((79899/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33176222073/1000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((79899/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c146 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((482667/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2667747/10000000) (δ := 16347/1000000000) (ψ := -72323/62500) 324 257
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t146 : ((79874972407/2000000000000 : ℚ) : ℝ) ≤ stT324 146 := by
  have hc : ((482567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79874972407/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((482567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c147 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-990617/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3755619/5000000) (δ := 16349/1000000000) (ψ := -72323/62500) 324 258
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t147 : ((-817130502279/10000000000000 : ℚ) : ℝ) ≤ stT324 147 := by
  have hc : ((-990717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-817130502279/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-990717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c148 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((345519/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2019681/10000000) (δ := 16349/1000000000) (ψ := -72323/62500) 324 258
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t148 : ((141986722593/2500000000000 : ℚ) : ℝ) ≤ stT324 148 := by
  have hc : ((345469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141986722593/2500000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((345469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c149 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((6111/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 171747/500000) (δ := 16349/1000000000) (ψ := -72323/62500) 324 258
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t149 : ((40030084353/2500000000000 : ℚ) : ℝ) ≤ stT324 149 := by
  have hc : ((48863/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40030084353/2500000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((48863/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c150 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-460611/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3427507/5000000) (δ := 8121/500000000) (ψ := -72323/62500) 324 259
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t150 : ((-376128324517/5000000000000 : ℚ) : ℝ) ≤ stT324 150 := by
  have hc : ((-460661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-376128324517/5000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-460661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c151 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((83141/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -184111/1250000) (δ := 8121/500000000) (ψ := -72323/62500) 324 259
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t151 : ((16912752557/250000000000 : ℚ) : ℝ) ≤ stT324 151 := by
  have hc : ((83131/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16912752557/250000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((83131/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c152 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((21323/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3873679/10000000) (δ := 8121/500000000) (ψ := -72323/62500) 324 259
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t152 : ((17214123861/10000000000000 : ℚ) : ℝ) ≤ stT324 152 := by
  have hc : ((21223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17214123861/10000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((21223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c153 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-53847/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -652279/1000000) (δ := 4067/250000000) (ψ := -72323/62500) 324 260
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t153 : ((-174151286089/2500000000000 : ℚ) : ℝ) ≤ stT324 153 := by
  have hc : ((-215413/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174151286089/2500000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-215413/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c154 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((878371/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1245883/10000000) (δ := 4067/250000000) (ψ := -72323/62500) 324 260
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t154 : ((353865046881/5000000000000 : ℚ) : ℝ) ≤ stT324 154 := by
  have hc : ((878271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((353865046881/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((878271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c155 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-27937/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1998421/5000000) (δ := 4067/250000000) (ψ := -72323/62500) 324 260
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t155 : ((-1125993957/500000000000 : ℚ) : ℝ) ≤ stT324 155 := by
  have hc : ((-28037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1125993957/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-28037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c156 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-21433/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1625523/2500000) (δ := 131/8000000) (ψ := -72323/62500) 324 261
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t156 : ((-34324280311/500000000000 : ℚ) : ℝ) ≤ stT324 156 := by
  have hc : ((-42871/50000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34324280311/500000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-42871/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c157 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((862533/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -663177/5000000) (δ := 131/8000000) (ψ := -72323/62500) 324 261
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t157 : ((344147851619/5000000000000 : ℚ) : ℝ) ≤ stT324 157 := by
  have hc : ((862433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((344147851619/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((862433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c158 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((44183/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1908249/5000000) (δ := 131/8000000) (ψ := -72323/62500) 324 261
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t158 : ((35070539231/10000000000000 : ℚ) : ℝ) ≤ stT324 158 := by
  have hc : ((44083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35070539231/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((44083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c159 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-113663/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3390507/5000000) (δ := 51/3125000) (ψ := -72323/62500) 324 262
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t159 : ((-45075291313/625000000000 : ℚ) : ℝ) ≤ stT324 159 := by
  have hc : ((-227351/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45075291313/625000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-227351/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c160 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((776909/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -851319/5000000) (δ := 51/3125000) (ψ := -72323/62500) 324 262
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t160 : ((614121114321/10000000000000 : ℚ) : ℝ) ≤ stT324 160 := by
  have hc : ((776809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((614121114321/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((776809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c161 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((115531/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3344067/10000000) (δ := 51/3125000) (ψ := -72323/62500) 324 262
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t161 : ((9101173091/500000000000 : ℚ) : ℝ) ≤ stT324 161 := by
  have hc : ((115481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9101173091/500000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((115481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c162 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-979619/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -918547/1250000) (δ := 16213/1000000000) (ψ := -72323/62500) 324 263
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t162 : ((-30789629013/400000000000 : ℚ) : ℝ) ≤ stT324 162 := by
  have hc : ((-979719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30789629013/400000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-979719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c163 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((146337/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2363717/10000000) (δ := 16213/1000000000) (ψ := -72323/62500) 324 263
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t163 : ((716252107/15625000000 : ℚ) : ℝ) ≤ stT324 163 := by
  have hc : ((18289/31250 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((716252107/15625000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((18289/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c164 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((254763/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 518081/2000000) (δ := 16213/1000000000) (ψ := -72323/62500) 324 263
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t164 : ((49724307721/1250000000000 : ℚ) : ℝ) ≤ stT324 164 := by
  have hc : ((254713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49724307721/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((254713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c165 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-990789/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1502879/2000000) (δ := 16213/1000000000) (ψ := -72323/62500) 324 263
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t165 : ((-771406095611/10000000000000 : ℚ) : ℝ) ≤ stT324 165 := by
  have hc : ((-990889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-771406095611/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-990889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c166 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((49689/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -659861/2000000) (δ := 16297/1000000000) (ψ := -72323/62500) 324 264
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t166 : ((771011887/40000000000 : ℚ) : ℝ) ≤ stT324 166 := by
  have hc : ((49669/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((771011887/40000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((49669/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c167 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((810229/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 391409/2500000) (δ := 16297/1000000000) (ψ := -72323/62500) 324 264
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t167 : ((626896453167/10000000000000 : ℚ) : ℝ) ≤ stT324 167 := by
  have hc : ((810129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((626896453167/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((810129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c168 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-8359/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6401417/10000000) (δ := 16297/1000000000) (ψ := -72323/62500) 324 264
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t168 : ((-161247053/2500000000 : ℚ) : ℝ) ≤ stT324 168 := by
  have hc : ((-209/250 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161247053/2500000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-209/250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c169 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-28369/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4499359/10000000) (δ := 16399/1000000000) (ψ := -72323/62500) 324 265
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t169 : ((-43663859253/2500000000000 : ℚ) : ℝ) ≤ stT324 169 := by
  have hc : ((-56763/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43663859253/2500000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-56763/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c170 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((993761/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 139699/5000000) (δ := 16399/1000000000) (ψ := -72323/62500) 324 265
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t170 : ((190525553801/2500000000000 : ℚ) : ℝ) ≤ stT324 170 := by
  have hc : ((993661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190525553801/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((993661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c171 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-17083/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5030129/10000000) (δ := 16399/1000000000) (ψ := -72323/62500) 324 265
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t171 : ((-163334633/5000000000 : ℚ) : ℝ) ≤ stT324 171 := by
  have hc : ((-17087/40000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163334633/5000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-17087/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c172 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-725063/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1190961/2000000) (δ := 4073/250000000) (ψ := -72323/62500) 324 266
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t172 : ((-552931711359/10000000000000 : ℚ) : ℝ) ≤ stT324 172 := by
  have hc : ((-725163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-552931711359/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-725163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c173 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((875821/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -629577/5000000) (δ := 4073/250000000) (ψ := -72323/62500) 324 266
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t173 : ((133159508097/2000000000000 : ℚ) : ℝ) ≤ stT324 173 := by
  have hc : ((875721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133159508097/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((875721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c174 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((25693/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3409443/10000000) (δ := 4073/250000000) (ψ := -72323/62500) 324 266
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t174 : ((19468335689/1250000000000 : ℚ) : ℝ) ≤ stT324 174 := by
  have hc : ((51361/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19468335689/1250000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((51361/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c175 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-996887/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7656653/10000000) (δ := 8109/500000000) (ψ := -72323/62500) 324 267
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t175 : ((-753651385923/10000000000000 : ℚ) : ℝ) ≤ stT324 175 := by
  have hc : ((-996987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-753651385923/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-996987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c176 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((173461/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3041273/10000000) (δ := 8109/500000000) (ψ := -72323/62500) 324 267
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t176 : ((65356698379/2500000000000 : ℚ) : ℝ) ≤ stT324 176 := by
  have hc : ((173411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65356698379/2500000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((173411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c177 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((814337/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61921/400000) (δ := 8109/500000000) (ψ := -72323/62500) 324 267
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t177 : ((306008992051/5000000000000 : ℚ) : ℝ) ≤ stT324 177 := by
  have hc : ((814237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((306008992051/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((814237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c178 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-766751/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6111403/10000000) (δ := 8109/500000000) (ψ := -72323/62500) 324 267
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t178 : ((-143694840933/2500000000000 : ℚ) : ℝ) ≤ stT324 178 := by
  have hc : ((-766851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143694840933/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-766851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c179 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-437379/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5058697/10000000) (δ := 8163/500000000) (ψ := -72323/62500) 324 268
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t179 : ((-81746888461/2500000000000 : ℚ) : ℝ) ≤ stT324 179 := by
  have hc : ((-437479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81746888461/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-437479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c180 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((976229/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -546187/10000000) (δ := 8163/500000000) (ψ := -72323/62500) 324 268
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t180 : ((145512526159/2000000000000 : ℚ) : ℝ) ≤ stT324 180 := by
  have hc : ((976129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145512526159/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((976129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c181 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-2877/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31531/80000) (δ := 8163/500000000) (ψ := -72323/62500) 324 268
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t181 : ((-435124893/1000000000000 : ℚ) : ℝ) ≤ stT324 181 := by
  have hc : ((-2927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-435124893/1000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-2927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c182 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-975883/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7303813/10000000) (δ := 1637/100000000) (ψ := -72323/62500) 324 269
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t182 : ((-578757919/8000000000 : ℚ) : ℝ) ≤ stT324 182 := by
  have hc : ((-975983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-578757919/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-975983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c183 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((411983/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1432709/5000000) (δ := 1637/100000000) (ψ := -72323/62500) 324 269
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t183 : ((304472563143/10000000000000 : ℚ) : ℝ) ≤ stT324 183 := by
  have hc : ((411883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((304472563143/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((411883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c184 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((814167/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 774379/5000000) (δ := 1637/100000000) (ψ := -72323/62500) 324 269
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t184 : ((600137519003/10000000000000 : ℚ) : ℝ) ≤ stT324 184 := by
  have hc : ((814067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((600137519003/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((814067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c185 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-144141/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5939039/10000000) (δ := 1637/100000000) (ψ := -72323/62500) 324 269
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t185 : ((-21197865923/400000000000 : ℚ) : ℝ) ≤ stT324 185 := by
  have hc : ((-144161/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21197865923/400000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-144161/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c186 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-556489/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -675297/1250000) (δ := 16263/1000000000) (ψ := -72323/62500) 324 270
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t186 : ((-102027773001/2500000000000 : ℚ) : ℝ) ≤ stT324 186 := by
  have hc : ((-556589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102027773001/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-556589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c187 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((911589/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -264789/2500000) (δ := 16263/1000000000) (ψ := -72323/62500) 324 270
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t187 : ((83318298001/1250000000000 : ℚ) : ℝ) ≤ stT324 187 := by
  have hc : ((911489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83318298001/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((911489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c188 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((263327/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3260817/10000000) (δ := 16263/1000000000) (ψ := -72323/62500) 324 270
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t188 : ((47994442137/2500000000000 : ℚ) : ℝ) ≤ stT324 188 := by
  have hc : ((263227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47994442137/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((263227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c189 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-992997/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1889487/2500000) (δ := 16263/1000000000) (ψ := -72323/62500) 324 270
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t189 : ((-722371806121/10000000000000 : ℚ) : ℝ) ≤ stT324 189 := by
  have hc : ((-993097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-722371806121/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-993097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c190 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((20537/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -775129/2000000) (δ := 16247/1000000000) (ψ := -72323/62500) 324 271
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t190 : ((3706638253/2500000000000 : ℚ) : ℝ) ≤ stT324 190 := by
  have hc : ((20437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3706638253/2500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((20437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c191 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((988689/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 376369/10000000) (δ := 16247/1000000000) (ψ := -72323/62500) 324 271
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t191 : ((357658648543/5000000000000 : ℚ) : ℝ) ≤ stT324 191 := by
  have hc : ((988589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((357658648543/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((988589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c192 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-134159/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1151527/2500000) (δ := 16247/1000000000) (ψ := -72323/62500) 324 271
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t192 : ((-12107128099/625000000000 : ℚ) : ℝ) ≤ stT324 192 := by
  have hc : ((-134209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12107128099/625000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-134209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c193 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-463593/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6894067/10000000) (δ := 8177/500000000) (ψ := -72323/62500) 324 272
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t193 : ((-41717206211/625000000000 : ℚ) : ℝ) ≤ stT324 193 := by
  have hc : ((-463643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41717206211/625000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-463643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c194 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((117127/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2707987/10000000) (δ := 8177/500000000) (ψ := -72323/62500) 324 272
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t194 : ((21018579429/625000000000 : ℚ) : ℝ) ≤ stT324 194 := by
  have hc : ((58551/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21018579429/625000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((58551/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c195 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((33401/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1456547/10000000) (δ := 8177/500000000) (ψ := -72323/62500) 324 272
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t195 : ((11958029629/200000000000 : ℚ) : ℝ) ≤ stT324 195 := by
  have hc : ((33397/40000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11958029629/200000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((33397/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c196 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-155073/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2799889/5000000) (δ := 8177/500000000) (ψ := -72323/62500) 324 272
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t196 : ((-27696082507/625000000000 : ℚ) : ℝ) ≤ stT324 196 := by
  have hc : ((-77549/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27696082507/625000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-77549/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c197 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-183401/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1197203/2000000) (δ := 16341/1000000000) (ψ := -72323/62500) 324 273
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t197 : ((-65342852823/1250000000000 : ℚ) : ℝ) ≤ stT324 197 := by
  have hc : ((-91713/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65342852823/1250000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-91713/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c198 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((729027/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -942371/5000000) (δ := 16341/1000000000) (ψ := -72323/62500) 324 273
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t198 : ((518025822163/10000000000000 : ℚ) : ℝ) ≤ stT324 198 := by
  have hc : ((728927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((518025822163/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((728927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c199 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((319211/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 548969/2500000) (δ := 16341/1000000000) (ψ := -72323/62500) 324 273
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t199 : ((226247168841/5000000000000 : ℚ) : ℝ) ≤ stT324 199 := by
  have hc : ((319161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226247168841/5000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((319161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c200 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-401289/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6256001/10000000) (δ := 16341/1000000000) (ψ := -72323/62500) 324 273
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t200 : ((-283789616273/5000000000000 : ℚ) : ℝ) ≤ stT324 200 := by
  have hc : ((-401339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-283789616273/5000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-401339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c201 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-111937/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2706003/5000000) (δ := 8117/500000000) (ψ := -72323/62500) 324 274
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t201 : ((-39484211061/1000000000000 : ℚ) : ℝ) ≤ stT324 201 := by
  have hc : ((-111957/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39484211061/1000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-111957/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c202 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((106113/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1392219/10000000) (δ := 8117/500000000) (ψ := -72323/62500) 324 274
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t202 : ((149303986997/2500000000000 : ℚ) : ℝ) ≤ stT324 202 := by
  have hc : ((212201/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149303986997/2500000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((212201/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c203 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((251763/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 651951/2500000) (δ := 8117/500000000) (ψ := -72323/62500) 324 274
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t203 : ((88333894803/2500000000000 : ℚ) : ℝ) ≤ stT324 203 := by
  have hc : ((251713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88333894803/2500000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((251713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c204 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-27329/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 411759/625000) (δ := 8117/500000000) (ψ := -72323/62500) 324 274
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t204 : ((-153090730637/2500000000000 : ℚ) : ℝ) ≤ stT324 204 := by
  have hc : ((-218657/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153090730637/2500000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-218657/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c205 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-473069/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5158919/10000000) (δ := 4069/250000000) (ψ := -72323/62500) 324 275
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t205 : ((-330475897839/10000000000000 : ℚ) : ℝ) ≤ stT324 205 := by
  have hc : ((-473169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-330475897839/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-473169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c206 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((883779/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1217297/10000000) (δ := 4069/250000000) (ψ := -72323/62500) 324 275
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t206 : ((615688320707/10000000000000 : ℚ) : ℝ) ≤ stT324 206 := by
  have hc : ((883679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((615688320707/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((883679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c207 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((46949/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2705209/10000000) (δ := 4069/250000000) (ψ := -72323/62500) 324 275
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t207 : ((4078107259/125000000000 : ℚ) : ℝ) ≤ stT324 207 := by
  have hc : ((46939/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4078107259/125000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((46939/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c208 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-878513/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3304421/5000000) (δ := 4069/250000000) (ψ := -72323/62500) 324 275
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t208 : ((-4759446621/78125000000 : ℚ) : ℝ) ≤ stT324 208 := by
  have hc : ((-878613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4759446621/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-878613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c209 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-492433/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5214199/10000000) (δ := 16383/1000000000) (ψ := -72323/62500) 324 276
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t209 : ((-68138492819/2000000000000 : ℚ) : ℝ) ≤ stT324 209 := by
  have hc : ((-492533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68138492819/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-492533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c210 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((171631/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -673913/5000000) (δ := 16383/1000000000) (ψ := -72323/62500) 324 276
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t210 : ((23684548943/400000000000 : ℚ) : ℝ) ≤ stT324 210 := by
  have hc : ((171611/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23684548943/400000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((171611/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c211 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((67531/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7813/31250) (δ := 16383/1000000000) (ψ := -72323/62500) 324 276
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t211 : ((23240812959/625000000000 : ℚ) : ℝ) ≤ stT324 211 := by
  have hc : ((135037/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23240812959/625000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((135037/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c212 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-819863/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6329921/10000000) (δ := 16383/1000000000) (ψ := -72323/62500) 324 276
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t212 : ((-563153048289/10000000000000 : ℚ) : ℝ) ≤ stT324 212 := by
  have hc : ((-819963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-563153048289/10000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-819963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c213 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-304861/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -695783/1250000) (δ := 16313/1000000000) (ψ := -72323/62500) 324 277
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t213 : ((-208921663179/5000000000000 : ℚ) : ℝ) ≤ stT324 213 := by
  have hc : ((-304911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-208921663179/5000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-304911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c214 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((94883/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -354461/2000000) (δ := 16313/1000000000) (ψ := -72323/62500) 324 277
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t214 : ((25940820297/500000000000 : ℚ) : ℝ) ≤ stT324 214 := by
  have hc : ((189741/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25940820297/500000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((189741/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c215 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((347791/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 400783/2000000) (δ := 16313/1000000000) (ψ := -72323/62500) 324 277
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t215 : ((118578637777/2500000000000 : ℚ) : ℝ) ≤ stT324 215 := by
  have hc : ((347741/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118578637777/2500000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((347741/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c216 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-670037/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5762639/10000000) (δ := 16313/1000000000) (ψ := -72323/62500) 324 277
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t216 : ((-227985298359/5000000000000 : ℚ) : ℝ) ≤ stT324 216 := by
  have hc : ((-670137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-227985298359/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-670137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c217 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-79/100 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1240803/2000000) (δ := 8103/500000000) (ψ := -72323/62500) 324 278
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t217 : ((-1072710869/20000000000 : ℚ) : ℝ) ≤ stT324 217 := by
  have hc : ((-7901/10000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1072710869/20000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-7901/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c218 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((273529/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1239939/5000000) (δ := 8103/500000000) (ψ := -72323/62500) 324 278
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t218 : ((37044644903/1000000000000 : ℚ) : ℝ) ≤ stT324 218 := by
  have hc : ((273479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37044644903/1000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((273479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c219 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((881909/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1227249/10000000) (δ := 8103/500000000) (ψ := -72323/62500) 324 278
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t219 : ((595870968233/10000000000000 : ℚ) : ℝ) ≤ stT324 219 := by
  have hc : ((881809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((595870968233/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((881809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c220 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-385899/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4917447/10000000) (δ := 8103/500000000) (ψ := -72323/62500) 324 278
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t220 : ((-1301202629/50000000000 : ℚ) : ℝ) ≤ stT324 220 := by
  have hc : ((-385999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1301202629/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-385999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c221 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-956863/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1779251/2500000) (δ := 3261/200000000) (ψ := -72323/62500) 324 279
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t221 : ((-643723172099/10000000000000 : ℚ) : ℝ) ≤ stT324 221 := by
  have hc : ((-956963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-643723172099/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-956963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c222 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((92821/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1730089/5000000) (δ := 3261/200000000) (ψ := -72323/62500) 324 279
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t222 : ((15565953319/1250000000000 : ℚ) : ℝ) ≤ stT324 222 := by
  have hc : ((92771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15565953319/1250000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((92771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c223 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((997401/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 90143/5000000) (δ := 3261/200000000) (ψ := -72323/62500) 324 279
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t223 : ((667841617349/10000000000000 : ℚ) : ℝ) ≤ stT324 223 := by
  have hc : ((997301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((667841617349/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((997301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c224 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((48989/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3804469/10000000) (δ := 3261/200000000) (ψ := -72323/62500) 324 279
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t224 : ((32665332017/10000000000000 : ℚ) : ℝ) ≤ stT324 224 := by
  have hc : ((48889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32665332017/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((48889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c225 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-19689/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7412533/10000000) (δ := 3261/200000000) (ψ := -72323/62500) 324 279
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t225 : ((-13127339897/200000000000 : ℚ) : ℝ) ≤ stT324 225 := by
  have hc : ((-19691/20000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13127339897/200000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-19691/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c226 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-305613/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -940689/2000000) (δ := 8103/250000000) (ψ := -72323/62500) 324 280
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t226 : ((-203357536183/10000000000000 : ℚ) : ℝ) ≤ stT324 226 := by
  have hc : ((-305713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-203357536183/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-305713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c227 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((450027/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -225451/2000000) (δ := 16391/1000000000) (ψ := -72323/62500) 324 280
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t227 : ((298660084371/5000000000000 : ℚ) : ℝ) ≤ stT324 227 := by
  have hc : ((449977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298660084371/5000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((449977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c228 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((562597/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2433181/10000000) (δ := 16391/1000000000) (ψ := -72323/62500) 324 280
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t228 : ((186261319101/5000000000000 : ℚ) : ℝ) ≤ stT324 228 := by
  have hc : ((562497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((186261319101/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((562497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c229 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-731439/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1195613/2000000) (δ := 16391/1000000000) (ψ := -72323/62500) 324 280
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t229 : ((-483414870441/10000000000000 : ℚ) : ℝ) ≤ stT324 229 := by
  have hc : ((-731539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-483414870441/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-731539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c230 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-394567/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1240097/2000000) (δ := 4071/250000000) (ψ := -72323/62500) 324 281
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t230 : ((-260202952077/5000000000000 : ℚ) : ℝ) ≤ stT324 230 := by
  have hc : ((-394617/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-260202952077/5000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-394617/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c231 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((238063/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2686381/10000000) (δ := 4071/250000000) (ψ := -72323/62500) 324 281
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t231 : ((156600891363/5000000000000 : ℚ) : ℝ) ≤ stT324 231 := by
  have hc : ((238013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156600891363/5000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((238013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c232 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((947651/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 162499/2000000) (δ := 4071/250000000) (ψ := -72323/62500) 324 281
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t232 : ((155524388283/2500000000000 : ℚ) : ℝ) ≤ stT324 232 := by
  have hc : ((947551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155524388283/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((947551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c233 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-147221/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2148193/5000000) (δ := 4071/250000000) (ψ := -72323/62500) 324 281
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t233 : ((-48256614081/5000000000000 : ℚ) : ℝ) ≤ stT324 233 := by
  have hc : ((-147321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48256614081/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-147321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c234 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-249843/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7765373/10000000) (δ := 4071/250000000) (ψ := -72323/62500) 324 281
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t234 : ((-40835989707/625000000000 : ℚ) : ℝ) ≤ stT324 234 := by
  have hc : ((-62467/62500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40835989707/625000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-62467/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c235 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-222691/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2244213/5000000) (δ := 8113/500000000) (ψ := -72323/62500) 324 282
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t235 : ((-145333030239/10000000000000 : ℚ) : ℝ) ≤ stT324 235 := by
  have hc : ((-222791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145333030239/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-222791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c236 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((182653/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1048923/10000000) (δ := 8113/500000000) (ψ := -72323/62500) 324 282
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t236 : ((1857560243/31250000000 : ℚ) : ℝ) ≤ stT324 236 := by
  have hc : ((182633/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1857560243/31250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((182633/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c237 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((290679/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 297/1250) (δ := 8113/500000000) (ψ := -72323/62500) 324 282
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t237 : ((188783588901/5000000000000 : ℚ) : ℝ) ≤ stT324 237 := by
  have hc : ((290629/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188783588901/5000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((290629/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c238 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-677093/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1157301/2000000) (δ := 8113/500000000) (ψ := -72323/62500) 324 282
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t238 : ((-109739802843/2500000000000 : ℚ) : ℝ) ≤ stT324 238 := by
  have hc : ((-677193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109739802843/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-677193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c239 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-862043/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6525209/10000000) (δ := 16333/1000000000) (ψ := -72323/62500) 324 283
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t239 : ((-557674613121/10000000000000 : ℚ) : ℝ) ≤ stT324 239 := by
  have hc : ((-862143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-557674613121/10000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-862143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c240 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((30843/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -628627/2000000) (δ := 16333/1000000000) (ψ := -72323/62500) 324 283
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t240 : ((19902609001/1000000000000 : ℚ) : ℝ) ≤ stT324 240 := by
  have hc : ((30833/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19902609001/1000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((30833/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c241 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((497979/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44969/2000000) (δ := 16333/1000000000) (ψ := -72323/62500) 324 283
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t241 : ((80185988231/1250000000000 : ℚ) : ℝ) ≤ stT324 241 := by
  have hc : ((497929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80185988231/1250000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((497929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c242 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((13879/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3578893/10000000) (δ := 16333/1000000000) (ψ := -72323/62500) 324 283
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t242 : ((1114415757/125000000000 : ℚ) : ℝ) ≤ stT324 242 := by
  have hc : ((13869/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1114415757/125000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((13869/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c243 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-930889/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 691909/1000000) (δ := 16333/1000000000) (ψ := -72323/62500) 324 283
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t243 : ((-597230374489/10000000000000 : ℚ) : ℝ) ≤ stT324 243 := by
  have hc : ((-930989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-597230374489/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-930989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c244 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-72033/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2731183/5000000) (δ := 8181/500000000) (ψ := -72323/62500) 324 284
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t244 : ((-18448979367/500000000000 : ℚ) : ℝ) ≤ stT324 244 := by
  have hc : ((-144091/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18448979367/500000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-144091/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c245 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((652587/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1074753/5000000) (δ := 32441/1000000000) (ψ := -72323/62500) 324 284
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t245 : ((104214571153/2500000000000 : ℚ) : ℝ) ≤ stT324 245 := by
  have hc : ((652487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104214571153/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((652487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c246 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((896069/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1149907/10000000) (δ := 8181/500000000) (ψ := -72323/62500) 324 284
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t246 : ((71406041393/1250000000000 : ℚ) : ℝ) ≤ stT324 246 := by
  have hc : ((895969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71406041393/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((895969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c247 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-202167/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 887183/2000000) (δ := 8181/500000000) (ψ := -72323/62500) 324 284
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t247 : ((-25739891619/2000000000000 : ℚ) : ℝ) ≤ stT324 247 := by
  have hc : ((-202267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25739891619/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-202267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c248 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-998311/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7708639/10000000) (δ := 8181/500000000) (ψ := -72323/62500) 324 284
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t248 : ((-633991983411/10000000000000 : ℚ) : ℝ) ≤ stT324 248 := by
  have hc : ((-998411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-633991983411/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-998411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c249 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-319427/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4739803/10000000) (δ := 3251/200000000) (ψ := -72323/62500) 324 285
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t249 : ((-8099689923/400000000000 : ℚ) : ℝ) ≤ stT324 249 := by
  have hc : ((-319527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8099689923/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-319527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c250 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((826859/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -746621/5000000) (δ := 3251/200000000) (ψ := -72323/62500) 324 285
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t250 : ((104577572669/2000000000000 : ℚ) : ℝ) ≤ stT324 250 := by
  have hc : ((826759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104577572669/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((826759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c251 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((383671/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 870139/5000000) (δ := 3251/200000000) (ψ := -72323/62500) 324 285
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t251 : ((121069636737/2500000000000 : ℚ) : ℝ) ≤ stT324 251 := by
  have hc : ((383621/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121069636737/2500000000000 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((383621/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c252 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-200941/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4960919/10000000) (δ := 3251/200000000) (ψ := -72323/62500) 324 285
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t252 : ((-126612471531/5000000000000 : ℚ) : ℝ) ≤ stT324 252 := by
  have hc : ((-200991/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).2
  have h0 : (0:ℝ) ≤ ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126612471531/5000000000000 : ℚ) : ℝ)
      = ((629941/10000000 : ℚ) : ℝ) * ((-200991/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c253 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-992079/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -94239/125000) (δ := 3251/200000000) (ψ := -72323/62500) 324 286
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t253 : ((-124755595281/2000000000000 : ℚ) : ℝ) ≤ stT324 253 := by
  have hc : ((-992179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124755595281/2000000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-992179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c254 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-33193/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -542979/1250000) (δ := 3251/200000000) (ψ := -72323/62500) 324 286
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t254 : ((-81405063/7812500000 : ℚ) : ℝ) ≤ stT324 254 := by
  have hc : ((-33213/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81405063/7812500000 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-33213/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c255 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((894073/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1161099/10000000) (δ := 3251/200000000) (ψ := -72323/62500) 324 286
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t255 : ((34989209247/625000000000 : ℚ) : ℝ) ≤ stT324 255 := by
  have hc : ((893973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).1
  have hw2 : ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39139/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34989209247/625000000000 : ℚ) : ℝ)
      = ((39139/625000 : ℚ) : ℝ) * ((893973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c256 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((347037/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50229/250000) (δ := 3251/200000000) (ψ := -72323/62500) 324 286
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t256 : ((346987/8000000 : ℚ) : ℝ) ≤ stT324 256 := by
  have hc : ((346987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).1
  have hw2 : ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((346987/8000000 : ℚ) : ℝ)
      = ((1/16 : ℚ) : ℝ) * ((346987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c257 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-118981/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2583513/5000000) (δ := 3251/200000000) (ψ := -72323/62500) 324 286
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t257 : ((-37116959849/1250000000000 : ℚ) : ℝ) ≤ stT324 257 := by
  have hc : ((-59503/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).2
  have h0 : (0:ℝ) ≤ ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37116959849/1250000000000 : ℚ) : ℝ)
      = ((623783/10000000 : ℚ) : ℝ) * ((-59503/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c258 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-61451/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3697651/5000000) (δ := 8181/500000000) (ψ := -72323/62500) 324 287
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t258 : ((-153046498017/2500000000000 : ℚ) : ℝ) ≤ stT324 258 := by
  have hc : ((-245829/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).2
  have h0 : (0:ℝ) ≤ ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153046498017/2500000000000 : ℚ) : ℝ)
      = ((622573/10000000 : ℚ) : ℝ) * ((-245829/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c259 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-13353/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4261817/10000000) (δ := 8181/500000000) (ψ := -72323/62500) 324 287
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t259 : ((-830336731/100000000000 : ℚ) : ℝ) ≤ stT324 259 := by
  have hc : ((-13363/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).2
  have h0 : (0:ℝ) ≤ ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-830336731/100000000000 : ℚ) : ℝ)
      = ((62137/1000000 : ℚ) : ℝ) * ((-13363/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c260 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((3591/4000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1140401/10000000) (δ := 8181/500000000) (ψ := -72323/62500) 324 287
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t260 : ((11133965869/200000000000 : ℚ) : ℝ) ≤ stT324 260 := by
  have hc : ((17953/20000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).1
  have hw2 : ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((620173/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11133965869/200000000000 : ℚ) : ℝ)
      = ((620173/10000000 : ℚ) : ℝ) * ((17953/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c261 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((35277/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1969027/10000000) (δ := 8181/500000000) (ψ := -72323/62500) 324 287
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t261 : ((341137557/7812500000 : ℚ) : ℝ) ≤ stT324 261 := by
  have hc : ((4409/6250 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).1
  have hw2 : ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((77373/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((341137557/7812500000 : ℚ) : ℝ)
      = ((77373/1250000 : ℚ) : ℝ) * ((4409/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c262 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-440201/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1266637/2500000) (δ := 24381/500000000) (ψ := -72323/62500) 324 287
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t262 : ((-272019278703/10000000000000 : ℚ) : ℝ) ≤ stT324 262 := by
  have hc : ((-440301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-272019278703/10000000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-440301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c263 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-248223/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7555721/10000000) (δ := 8167/500000000) (ψ := -72323/62500) 324 288
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t263 : ((-19134552437/312500000000 : ℚ) : ℝ) ≤ stT324 263 := by
  have hc : ((-31031/31250 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).2
  have h0 : (0:ℝ) ≤ ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19134552437/312500000000 : ℚ) : ℝ)
      = ((616627/10000000 : ℚ) : ℝ) * ((-31031/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c264 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-6877/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -448169/1000000) (δ := 24367/500000000) (ψ := -72323/62500) 324 288
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t264 : ((-16937711889/1250000000000 : ℚ) : ℝ) ≤ stT324 264 := by
  have hc : ((-55041/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).2
  have h0 : (0:ℝ) ≤ ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16937711889/1250000000000 : ℚ) : ℝ)
      = ((307729/5000000 : ℚ) : ℝ) * ((-55041/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c265 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((210781/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1419323/10000000) (δ := 8167/500000000) (ψ := -72323/62500) 324 288
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t265 : ((6473317851/125000000000 : ℚ) : ℝ) ≤ stT324 265 := by
  have hc : ((52689/62500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6473317851/125000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((52689/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c266 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((794497/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 815771/5000000) (δ := 8167/500000000) (ψ := -72323/62500) 324 288
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t266 : ((487075782183/10000000000000 : ℚ) : ℝ) ≤ stT324 266 := by
  have hc : ((794397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).1
  have hw2 : ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((613139/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((487075782183/10000000000000 : ℚ) : ℝ)
      = ((613139/10000000 : ℚ) : ℝ) * ((794397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c267 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-146597/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 934181/2000000) (δ := 8167/500000000) (ψ := -72323/62500) 324 288
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t267 : ((-89746644177/5000000000000 : ℚ) : ℝ) ≤ stT324 267 := by
  have hc : ((-146647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89746644177/5000000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-146647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c268 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-998077/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 481183/625000) (δ := 8167/500000000) (ψ := -72323/62500) 324 288
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t268 : ((-19054200753/312500000000 : ℚ) : ℝ) ≤ stT324 268 := by
  have hc : ((-998177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19054200753/312500000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-998177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c269 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-206667/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4992271/10000000) (δ := 16227/1000000000) (ψ := -72323/62500) 324 289
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t269 : ((-126037628787/5000000000000 : ℚ) : ℝ) ≤ stT324 269 := by
  have hc : ((-206717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).2
  have h0 : (0:ℝ) ≤ ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126037628787/5000000000000 : ℚ) : ℝ)
      = ((609711/10000000 : ℚ) : ℝ) * ((-206717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c270 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((700517/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -397337/2000000) (δ := 16227/1000000000) (ψ := -72323/62500) 324 289
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t270 : ((21312988893/500000000000 : ℚ) : ℝ) ≤ stT324 270 := by
  have hc : ((700417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21312988893/500000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((700417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c271 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((919841/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 251951/2500000) (δ := 16227/1000000000) (ψ := -72323/62500) 324 289
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t271 : ((17459443403/312500000000 : ℚ) : ℝ) ≤ stT324 271 := by
  have hc : ((919741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17459443403/312500000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((919741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c272 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-25679/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 997799/2500000) (δ := 16227/1000000000) (ψ := -72323/62500) 324 289
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t272 : ((-781541943/500000000000 : ℚ) : ℝ) ≤ stT324 272 := by
  have hc : ((-25779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).2
  have h0 : (0:ℝ) ≤ ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-781541943/500000000000 : ℚ) : ℝ)
      = ((30317/500000 : ℚ) : ℝ) * ((-25779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c273 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-937253/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6963653/10000000) (δ := 16227/1000000000) (ψ := -72323/62500) 324 289
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t273 : ((-141828070371/2500000000000 : ℚ) : ℝ) ≤ stT324 273 := by
  have hc : ((-937353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141828070371/2500000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-937353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c274 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-675951/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2891313/5000000) (δ := 4071/250000000) (ψ := -72323/62500) 324 290
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t274 : ((-408417958273/10000000000000 : ℚ) : ℝ) ≤ stT324 274 := by
  have hc : ((-676051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-408417958273/10000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-676051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c275 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((42417/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2831877/10000000) (δ := 4071/250000000) (ψ := -72323/62500) 324 290
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t275 : ((12786176977/500000000000 : ℚ) : ℝ) ≤ stT324 275 := by
  have hc : ((42407/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).1
  have hw2 : ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((301511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12786176977/500000000000 : ℚ) : ℝ)
      = ((301511/5000000 : ℚ) : ℝ) * ((42407/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c276 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((999063/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 108261/10000000) (δ := 4071/250000000) (ψ := -72323/62500) 324 290
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t276 : ((601304799627/10000000000000 : ℚ) : ℝ) ≤ stT324 276 := by
  have hc : ((998963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((601304799627/10000000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((998963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c277 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((348229/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 759447/2500000) (δ := 4071/250000000) (ψ := -72323/62500) 324 290
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t277 : ((209170176489/10000000000000 : ℚ) : ℝ) ≤ stT324 277 := by
  have hc : ((348129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209170176489/10000000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((348129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c278 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-362793/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 186147/312500) (δ := 4071/250000000) (ψ := -72323/62500) 324 290
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t278 : ((-217619080523/5000000000000 : ℚ) : ℝ) ≤ stT324 278 := by
  have hc : ((-362843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).2
  have h0 : (0:ℝ) ≤ ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217619080523/5000000000000 : ℚ) : ℝ)
      = ((599761/10000000 : ℚ) : ℝ) * ((-362843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c279 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-459661/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6842873/10000000) (δ := 16391/1000000000) (ψ := -72323/62500) 324 291
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t279 : ((-55044416007/1000000000000 : ℚ) : ℝ) ≤ stT324 279 := by
  have hc : ((-459711/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).2
  have h0 : (0:ℝ) ≤ ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55044416007/1000000000000 : ℚ) : ℝ)
      = ((119737/2000000 : ℚ) : ℝ) * ((-459711/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c280 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-7113/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1972387/5000000) (δ := 16391/1000000000) (ψ := -72323/62500) 324 291
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t280 : ((-862119399/2000000000000 : ℚ) : ℝ) ≤ stT324 280 := by
  have hc : ((-7213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-862119399/2000000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-7213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c281 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((911923/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -264281/2500000) (δ := 16391/1000000000) (ψ := -72323/62500) 324 291
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t281 : ((543947098827/10000000000000 : ℚ) : ℝ) ≤ stT324 281 := by
  have hc : ((911823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).1
  have hw2 : ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((596549/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((543947098827/10000000000000 : ℚ) : ℝ)
      = ((596549/10000000 : ℚ) : ℝ) * ((911823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c282 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((746421/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11377/62500) (δ := 16391/1000000000) (ψ := -72323/62500) 324 291
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t282 : ((444427438611/10000000000000 : ℚ) : ℝ) ≤ stT324 282 := by
  have hc : ((746321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((444427438611/10000000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((746321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c283 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-74889/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2343779/5000000) (δ := 16391/1000000000) (ψ := -72323/62500) 324 291
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t283 : ((-22265901623/1250000000000 : ℚ) : ℝ) ≤ stT324 283 := by
  have hc : ((-37457/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).2
  have h0 : (0:ℝ) ≤ ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22265901623/1250000000000 : ℚ) : ℝ)
      = ((594439/10000000 : ℚ) : ℝ) * ((-37457/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c284 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-24809/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 471547/625000) (δ := 16391/1000000000) (ψ := -72323/62500) 324 291
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t284 : ((-29445841593/500000000000 : ℚ) : ℝ) ≤ stT324 284 := by
  have hc : ((-49623/50000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).2
  have h0 : (0:ℝ) ≤ ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29445841593/500000000000 : ℚ) : ℝ)
      = ((593391/10000000 : ℚ) : ℝ) * ((-49623/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c285 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-105501/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5316143/10000000) (δ := 3261/200000000) (ψ := -72323/62500) 324 292
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t285 : ((-62505258829/2000000000000 : ℚ) : ℝ) ≤ stT324 285 := by
  have hc : ((-105521/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62505258829/2000000000000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-105521/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c286 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((273683/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -619739/2500000) (δ := 3261/200000000) (ψ := -72323/62500) 324 292
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t286 : ((10112654781/312500000000 : ℚ) : ℝ) ≤ stT324 286 := by
  have hc : ((273633/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).1
  have hw2 : ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((36957/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10112654781/312500000000 : ℚ) : ℝ)
      = ((36957/625000 : ℚ) : ℝ) * ((273633/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c287 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((123789/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 87067/2500000) (δ := 3261/200000000) (ψ := -72323/62500) 324 292
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t287 : ((146125832393/2500000000000 : ℚ) : ℝ) ≤ stT324 287 := by
  have hc : ((247553/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).1
  have hw2 : ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((590281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146125832393/2500000000000 : ℚ) : ℝ)
      = ((590281/10000000 : ℚ) : ℝ) * ((247553/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c288 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((149933/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 316561/1000000) (δ := 3261/200000000) (ψ := -72323/62500) 324 292
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t288 : ((17663861433/1000000000000 : ℚ) : ℝ) ≤ stT324 288 := by
  have hc : ((149883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17663861433/1000000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((149883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c289 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-730119/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 373327/625000) (δ := 3261/200000000) (ψ := -72323/62500) 324 292
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t289 : ((-107385275921/2500000000000 : ℚ) : ℝ) ≤ stT324 289 := by
  have hc : ((-730219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).2
  have h0 : (0:ℝ) ≤ ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107385275921/2500000000000 : ℚ) : ℝ)
      = ((147059/2500000 : ℚ) : ℝ) * ((-730219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c290 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-466723/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1734187/2500000) (δ := 3241/200000000) (ψ := -72323/62500) 324 293
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t290 : ((-274098907833/5000000000000 : ℚ) : ℝ) ≤ stT324 290 := by
  have hc : ((-466773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).2
  have h0 : (0:ℝ) ≤ ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274098907833/5000000000000 : ℚ) : ℝ)
      = ((587221/10000000 : ℚ) : ℝ) * ((-466773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c291 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-44241/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -829697/2000000) (δ := 3241/200000000) (ψ := -72323/62500) 324 293
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t291 : ((-25963871401/5000000000000 : ℚ) : ℝ) ≤ stT324 291 := by
  have hc : ((-44291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).2
  have h0 : (0:ℝ) ≤ ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25963871401/5000000000000 : ℚ) : ℝ)
      = ((586211/10000000 : ℚ) : ℝ) * ((-44291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c292 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((853631/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1369699/10000000) (δ := 3241/200000000) (ψ := -72323/62500) 324 293
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t292 : ((99898121771/2000000000000 : ℚ) : ℝ) ≤ stT324 292 := by
  have hc : ((853531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).1
  have hw2 : ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117041/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99898121771/2000000000000 : ℚ) : ℝ)
      = ((117041/2000000 : ℚ) : ℝ) * ((853531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c293 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((169471/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1399529/10000000) (δ := 3241/200000000) (ψ := -72323/62500) 324 293
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t293 : ((49497145453/1000000000000 : ℚ) : ℝ) ≤ stT324 293 := by
  have hc : ((169451/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).1
  have hw2 : ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((292103/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49497145453/1000000000000 : ℚ) : ℝ)
      = ((292103/5000000 : ℚ) : ℝ) * ((169451/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c294 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-46391/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51991/125000) (δ := 3241/200000000) (ψ := -72323/62500) 324 293
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t294 : ((-6771237123/1250000000000 : ℚ) : ℝ) ≤ stT324 294 := by
  have hc : ((-46441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6771237123/1250000000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-46441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c295 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-929513/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1727429/2500000) (δ := 3241/200000000) (ψ := -72323/62500) 324 293
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t295 : ((-541242069699/10000000000000 : ℚ) : ℝ) ≤ stT324 295 := by
  have hc : ((-929613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).2
  have h0 : (0:ℝ) ≤ ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-541242069699/10000000000000 : ℚ) : ℝ)
      = ((582223/10000000 : ℚ) : ℝ) * ((-929613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c296 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-376317/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3028563/5000000) (δ := 2039/125000000) (ψ := -72323/62500) 324 294
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t296 : ((-218759178713/5000000000000 : ℚ) : ℝ) ≤ stT324 296 := by
  have hc : ((-376367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).2
  have h0 : (0:ℝ) ≤ ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218759178713/5000000000000 : ℚ) : ℝ)
      = ((581239/10000000 : ℚ) : ℝ) * ((-376367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c297 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((238383/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3325239/10000000) (δ := 2039/125000000) (ψ := -72323/62500) 324 294
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t297 : ((69132808507/5000000000000 : ℚ) : ℝ) ≤ stT324 297 := by
  have hc : ((238283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).1
  have hw2 : ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290129/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69132808507/5000000000000 : ℚ) : ℝ)
      = ((290129/5000000 : ℚ) : ℝ) * ((238283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c298 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((242773/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -301293/5000000) (δ := 2039/125000000) (ψ := -72323/62500) 324 294
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t298 : ((8788752027/156250000000 : ℚ) : ℝ) ≤ stT324 298 := by
  have hc : ((60687/62500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8788752027/156250000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((60687/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c299 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((664181/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 422199/2000000) (δ := 2039/125000000) (ψ := -72323/62500) 324 294
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t299 : ((192023669717/5000000000000 : ℚ) : ℝ) ≤ stT324 299 := by
  have hc : ((664081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).1
  have hw2 : ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((289157/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192023669717/5000000000000 : ℚ) : ℝ)
      = ((289157/5000000 : ℚ) : ℝ) * ((664081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c300 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-34797/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 300969/625000) (δ := 2039/125000000) (ψ := -72323/62500) 324 294
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t300 : ((-20095856257/1000000000000 : ℚ) : ℝ) ≤ stT324 300 := by
  have hc : ((-34807/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).2
  have h0 : (0:ℝ) ≤ ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20095856257/1000000000000 : ℚ) : ℝ)
      = ((577351/10000000 : ℚ) : ℝ) * ((-34807/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c301 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-198121/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3755511/5000000) (δ := 2039/125000000) (ψ := -72323/62500) 324 294
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t301 : ((-114206689131/2000000000000 : ℚ) : ℝ) ≤ stT324 301 := by
  have hc : ((-198141/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).2
  have h0 : (0:ℝ) ≤ ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114206689131/2000000000000 : ℚ) : ℝ)
      = ((576391/10000000 : ℚ) : ℝ) * ((-198141/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c302 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-295919/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2755167/5000000) (δ := 32/1953125) (ψ := -72323/62500) 324 295
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t302 : ((-42577804371/1250000000000 : ℚ) : ℝ) ≤ stT324 302 := by
  have hc : ((-295969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42577804371/1250000000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-295969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c303 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((84779/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -708159/2500000) (δ := 32/1953125) (ψ := -72323/62500) 324 295
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t303 : ((12173172339/500000000000 : ℚ) : ℝ) ≤ stT324 303 := by
  have hc : ((84759/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).1
  have hw2 : ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143621/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12173172339/500000000000 : ℚ) : ℝ)
      = ((143621/2500000 : ℚ) : ℝ) * ((84759/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c304 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((199571/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -163767/10000000) (δ := 32/1953125) (ψ := -72323/62500) 324 295
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t304 : ((114450280989/2000000000000 : ℚ) : ℝ) ≤ stT324 304 := by
  have hc : ((199551/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).1
  have hw2 : ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114450280989/2000000000000 : ℚ) : ℝ)
      = ((573539/10000000 : ℚ) : ℝ) * ((199551/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c305 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((135389/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2496273/10000000) (δ := 32/1953125) (ψ := -72323/62500) 324 295
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t305 : ((9688644459/312500000000 : ℚ) : ℝ) ≤ stT324 305 := by
  have hc : ((33841/62500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).1
  have hw2 : ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((286299/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9688644459/312500000000 : ℚ) : ℝ)
      = ((286299/5000000 : ℚ) : ℝ) * ((33841/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c306 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-1466/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5147727/10000000) (δ := 32/1953125) (ψ := -72323/62500) 324 295
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t306 : ((-6705881091/250000000000 : ℚ) : ℝ) ≤ stT324 306 := by
  have hc : ((-23461/50000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).2
  have h0 : (0:ℝ) ≤ ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6705881091/250000000000 : ℚ) : ℝ)
      = ((285831/5000000 : ℚ) : ℝ) * ((-23461/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c307 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-999677/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7790433/10000000) (δ := 32/1953125) (ψ := -72323/62500) 324 295
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t307 : ((-570603726987/10000000000000 : ℚ) : ℝ) ≤ stT324 307 := by
  have hc : ((-999777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).2
  have h0 : (0:ℝ) ≤ ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-570603726987/10000000000000 : ℚ) : ℝ)
      = ((570731/10000000 : ℚ) : ℝ) * ((-999777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c308 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-516337/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -528341/1000000) (δ := 4069/250000000) (ψ := -72323/62500) 324 296
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t308 : ((-294267351911/10000000000000 : ℚ) : ℝ) ≤ stT324 308 := by
  have hc : ((-516437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).2
  have h0 : (0:ℝ) ≤ ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-294267351911/10000000000000 : ℚ) : ℝ)
      = ((569803/10000000 : ℚ) : ℝ) * ((-516437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c309 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((9723/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -531559/2000000) (δ := 4069/250000000) (ψ := -72323/62500) 324 296
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t309 : ((69126031/2500000000 : ℚ) : ℝ) ≤ stT324 309 := by
  have hc : ((9721/20000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69126031/2500000000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((9721/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c310 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((249967/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8137/2000000) (δ := 4069/250000000) (ψ := -72323/62500) 324 296
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t310 : ((70978654131/1250000000000 : ℚ) : ℝ) ≤ stT324 310 := by
  have hc : ((124971/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).1
  have hw2 : ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567961/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70978654131/1250000000000 : ℚ) : ℝ)
      = ((567961/10000000 : ℚ) : ℝ) * ((124971/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c311 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((517189/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1284041/5000000) (δ := 4069/250000000) (ψ := -72323/62500) 324 296
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t311 : ((293213766183/10000000000000 : ℚ) : ℝ) ≤ stT324 311 := by
  have hc : ((517089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).1
  have hw2 : ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((293213766183/10000000000000 : ℚ) : ℝ)
      = ((567047/10000000 : ℚ) : ℝ) * ((517089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c312 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-476387/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 646043/1250000) (δ := 4069/250000000) (ψ := -72323/62500) 324 296
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t312 : ((-269757873693/10000000000000 : ℚ) : ℝ) ≤ stT324 312 := by
  have hc : ((-476487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-269757873693/10000000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-476487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c313 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-999299/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 970043/1250000) (δ := 4069/250000000) (ψ := -72323/62500) 324 296
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t313 : ((-282447147183/5000000000000 : ℚ) : ℝ) ≤ stT324 313 := by
  have hc : ((-999399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-282447147183/5000000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-999399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c314 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-54363/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5363881/10000000) (δ := 8117/500000000) (ψ := -72323/62500) 324 297
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t314 : ((-30684478209/1000000000000 : ℚ) : ℝ) ≤ stT324 314 := by
  have hc : ((-54373/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).2
  have h0 : (0:ℝ) ≤ ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30684478209/1000000000000 : ℚ) : ℝ)
      = ((564333/10000000 : ℚ) : ℝ) * ((-54373/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c315 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((219941/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -697081/2500000) (δ := 8117/500000000) (ψ := -72323/62500) 324 297
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t315 : ((30973626369/1250000000000 : ℚ) : ℝ) ≤ stT324 315 := by
  have hc : ((219891/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30973626369/1250000000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((219891/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c316 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((996097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55237/2500000) (δ := 8117/500000000) (ψ := -72323/62500) 324 297
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t316 : ((560291140371/10000000000000 : ℚ) : ℝ) ≤ stT324 316 := by
  have hc : ((995997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((560291140371/10000000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((995997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c317 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((296789/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2338247/10000000) (δ := 8117/500000000) (ψ := -72323/62500) 324 297
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t317 : ((33332988609/1000000000000 : ℚ) : ℝ) ≤ stT324 317 := by
  have hc : ((296739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).1
  have hw2 : ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((112331/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33332988609/1000000000000 : ℚ) : ℝ)
      = ((112331/2000000 : ℚ) : ℝ) * ((296739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c318 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-187767/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4889423/10000000) (δ := 8117/500000000) (ψ := -72323/62500) 324 297
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t318 : ((-105322702541/5000000000000 : ℚ) : ℝ) ≤ stT324 318 := by
  have hc : ((-187817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).2
  have h0 : (0:ℝ) ≤ ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105322702541/5000000000000 : ℚ) : ℝ)
      = ((560773/10000000 : ℚ) : ℝ) * ((-187817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c319 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-985833/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7432661/10000000) (δ := 8117/500000000) (ψ := -72323/62500) 324 297
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t319 : ((-552016985169/10000000000000 : ℚ) : ℝ) ≤ stT324 319 := by
  have hc : ((-985933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-552016985169/10000000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-985933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c320 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-663337/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1435041/2500000) (δ := 16341/1000000000) (ψ := -72323/62500) 324 298
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t320 : ((-370872561429/10000000000000 : ℚ) : ℝ) ≤ stT324 320 := by
  have hc : ((-663437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-370872561429/10000000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-663437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c321 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((140903/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1606401/5000000) (δ := 16341/1000000000) (ψ := -72323/62500) 324 298
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t321 : ((15723279537/1000000000000 : ℚ) : ℝ) ≤ stT324 321 := by
  have hc : ((140853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).1
  have hw2 : ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111629/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15723279537/1000000000000 : ℚ) : ℝ)
      = ((111629/2000000 : ℚ) : ℝ) * ((140853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c322 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((120223/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -346689/5000000) (δ := 16341/1000000000) (ψ := -72323/62500) 324 298
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t322 : ((66990667019/1250000000000 : ℚ) : ℝ) ≤ stT324 322 := by
  have hc : ((240421/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66990667019/1250000000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((240421/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c323 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((746967/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181827/1000000) (δ := 16341/1000000000) (ψ := -72323/62500) 324 298
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t323 : ((207783627469/5000000000000 : ℚ) : ℝ) ≤ stT324 323 := by
  have hc : ((746867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).1
  have hw2 : ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278207/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((207783627469/5000000000000 : ℚ) : ℝ)
      = ((278207/5000000 : ℚ) : ℝ) * ((746867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c324 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-157403/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2161071/5000000) (δ := 16341/1000000000) (ψ := -72323/62500) 324 298
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t324 : ((-21875434167/2500000000000 : ℚ) : ℝ) ≤ stT324 324 := by
  have hc : ((-157503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).2
  have h0 : (0:ℝ) ≤ ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21875434167/2500000000000 : ℚ) : ℝ)
      = ((138889/2500000 : ℚ) : ℝ) * ((-157503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c325 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-915399/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3409119/5000000) (δ := 16341/1000000000) (ψ := -72323/62500) 324 298
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t325 : ((-507828210799/10000000000000 : ℚ) : ℝ) ≤ stT324 325 := by
  have hc : ((-915499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).2
  have h0 : (0:ℝ) ≤ ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-507828210799/10000000000000 : ℚ) : ℝ)
      = ((554701/10000000 : ℚ) : ℝ) * ((-915499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c326 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-417931/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1600311/2500000) (δ := 3271/200000000) (ψ := -72323/62500) 324 299
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t326 : ((-231498358869/5000000000000 : ℚ) : ℝ) ≤ stT324 326 := by
  have hc : ((-417981/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).2
  have h0 : (0:ℝ) ≤ ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-231498358869/5000000000000 : ℚ) : ℝ)
      = ((553849/10000000 : ℚ) : ℝ) * ((-417981/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c327 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((1323/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -490047/1250000) (δ := 3271/200000000) (ψ := -72323/62500) 324 299
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t327 : ((703970273/5000000000000 : ℚ) : ℝ) ≤ stT324 327 := by
  have hc : ((1273/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).1
  have hw2 : ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((553001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((703970273/5000000000000 : ℚ) : ℝ)
      = ((553001/10000000 : ℚ) : ℝ) * ((1273/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c328 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((837111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1447041/10000000) (δ := 3271/200000000) (ψ := -72323/62500) 324 299
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t328 : ((462161482727/10000000000000 : ℚ) : ℝ) ≤ stT324 328 := by
  have hc : ((837011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).1
  have hw2 : ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((552157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((462161482727/10000000000000 : ℚ) : ℝ)
      = ((552157/10000000 : ℚ) : ℝ) * ((837011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c329 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((459063/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 25467/250000) (δ := 3271/200000000) (ψ := -72323/62500) 324 299
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t329 : ((253061670121/5000000000000 : ℚ) : ℝ) ≤ stT324 329 := by
  have hc : ((459013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).1
  have hw2 : ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((551317/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((253061670121/5000000000000 : ℚ) : ℝ)
      = ((551317/10000000 : ℚ) : ℝ) * ((459013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c330 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((89523/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3476949/10000000) (δ := 3271/200000000) (ψ := -72323/62500) 324 299
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t330 : ((49253186513/5000000000000 : ℚ) : ℝ) ≤ stT324 330 := by
  have hc : ((89473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).1
  have hw2 : ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((550481/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49253186513/5000000000000 : ℚ) : ℝ)
      = ((550481/10000000 : ℚ) : ℝ) * ((89473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c331 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-179393/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2963883/5000000) (δ := 3271/200000000) (ψ := -72323/62500) 324 299
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t331 : ((-986171037/25000000000 : ℚ) : ℝ) ≤ stT324 331 := by
  have hc : ((-89709/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-986171037/25000000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-89709/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c332 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-489337/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7336751/10000000) (δ := 2031/125000000) (ψ := -72323/62500) 324 300
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t332 : ((-134293176057/2500000000000 : ℚ) : ℝ) ≤ stT324 332 := by
  have hc : ((-489387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).2
  have h0 : (0:ℝ) ≤ ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134293176057/2500000000000 : ℚ) : ℝ)
      = ((274411/5000000 : ℚ) : ℝ) * ((-489387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c333 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-189851/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1225169/2500000) (δ := 2031/125000000) (ψ := -72323/62500) 324 300
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t333 : ((-104065178297/5000000000000 : ℚ) : ℝ) ≤ stT324 333 := by
  have hc : ((-189901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).2
  have h0 : (0:ℝ) ≤ ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104065178297/5000000000000 : ℚ) : ℝ)
      = ((547997/10000000 : ℚ) : ℝ) * ((-189901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c334 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((549729/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2471891/10000000) (δ := 2031/125000000) (ψ := -72323/62500) 324 300
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t334 : ((12029729923/400000000000 : ℚ) : ℝ) ≤ stT324 334 := by
  have hc : ((549629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12029729923/400000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((549629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c335 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((999797/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10063/2000000) (δ := 2031/125000000) (ψ := -72323/62500) 324 300
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t335 : ((273096226763/5000000000000 : ℚ) : ℝ) ≤ stT324 335 := by
  have hc : ((999697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((273096226763/5000000000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((999697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c336 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((292633/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2363971/10000000) (δ := 2031/125000000) (ψ := -72323/62500) 324 300
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t336 : ((19952112519/625000000000 : ℚ) : ℝ) ≤ stT324 336 := by
  have hc : ((292583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19952112519/625000000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((292583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c337 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-82819/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4771129/10000000) (δ := 2031/125000000) (ψ := -72323/62500) 324 300
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t337 : ((-2256401317/125000000000 : ℚ) : ℝ) ≤ stT324 337 := by
  have hc : ((-20711/62500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).2
  have h0 : (0:ℝ) ≤ ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2256401317/125000000000 : ℚ) : ℝ)
      = ((108947/2000000 : ℚ) : ℝ) * ((-20711/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c338 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-962923/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3585539/5000000) (δ := 2031/125000000) (ψ := -72323/62500) 324 300
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t338 : ((-523816137367/10000000000000 : ℚ) : ℝ) ≤ stT324 338 := by
  have hc : ((-963023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).2
  have h0 : (0:ℝ) ≤ ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-523816137367/10000000000000 : ℚ) : ℝ)
      = ((543929/10000000 : ℚ) : ℝ) * ((-963023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c339 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-775031/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3071951/5000000) (δ := 16263/1000000000) (ψ := -72323/62500) 324 301
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t339 : ((-210496899753/5000000000000 : ℚ) : ℝ) ≤ stT324 339 := by
  have hc : ((-775131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-210496899753/5000000000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-775131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c340 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((33763/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3758047/10000000) (δ := 16263/1000000000) (ψ := -72323/62500) 324 301
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t340 : ((9141718219/2500000000000 : ℚ) : ℝ) ≤ stT324 340 := by
  have hc : ((33713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).1
  have hw2 : ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9141718219/2500000000000 : ℚ) : ℝ)
      = ((271163/5000000 : ℚ) : ℝ) * ((33713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c341 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((851637/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1379239/10000000) (δ := 16263/1000000000) (ψ := -72323/62500) 324 301
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t341 : ((46113283161/1000000000000 : ℚ) : ℝ) ≤ stT324 341 := by
  have hc : ((851537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).1
  have hw2 : ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((54153/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46113283161/1000000000000 : ℚ) : ℝ)
      = ((54153/1000000 : ℚ) : ℝ) * ((851537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c342 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((922197/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 248171/2500000) (δ := 16263/1000000000) (ψ := -72323/62500) 324 301
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t342 : ((249306443793/5000000000000 : ℚ) : ℝ) ≤ stT324 342 := by
  have hc : ((922097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).1
  have hw2 : ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((270369/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249306443793/5000000000000 : ℚ) : ℝ)
      = ((270369/5000000 : ℚ) : ℝ) * ((922097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c343 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((14111/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3357641/10000000) (δ := 16263/1000000000) (ψ := -72323/62500) 324 301
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t343 : ((30463382631/2500000000000 : ℚ) : ℝ) ≤ stT324 343 := by
  have hc : ((56419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30463382631/2500000000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((56419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c344 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-327993/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5715713/10000000) (δ := 16263/1000000000) (ψ := -72323/62500) 324 301
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t344 : ((-44217244013/1250000000000 : ℚ) : ℝ) ≤ stT324 344 := by
  have hc : ((-328043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).2
  have h0 : (0:ℝ) ≤ ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44217244013/1250000000000 : ℚ) : ℝ)
      = ((134791/2500000 : ℚ) : ℝ) * ((-328043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c345 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-996373/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3820491/5000000) (δ := 1637/100000000) (ψ := -72323/62500) 324 302
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t345 : ((-268241563343/5000000000000 : ℚ) : ℝ) ≤ stT324 345 := by
  have hc : ((-996473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).2
  have h0 : (0:ℝ) ≤ ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-268241563343/5000000000000 : ℚ) : ℝ)
      = ((269191/5000000 : ℚ) : ℝ) * ((-996473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c346 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-520847/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5296599/10000000) (δ := 1637/100000000) (ψ := -72323/62500) 324 302
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t346 : ((-70015797747/2500000000000 : ℚ) : ℝ) ≤ stT324 346 := by
  have hc : ((-520947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).2
  have h0 : (0:ℝ) ≤ ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70015797747/2500000000000 : ℚ) : ℝ)
      = ((134401/2500000 : ℚ) : ℝ) * ((-520947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c347 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((23601/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2958939/10000000) (δ := 1637/100000000) (ψ := -72323/62500) 324 302
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t347 : ((12666322453/625000000000 : ℚ) : ℝ) ≤ stT324 347 := by
  have hc : ((94379/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12666322453/625000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((94379/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c348 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((193723/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -314001/5000000) (δ := 1637/100000000) (ψ := -72323/62500) 324 302
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t348 : ((12979456921/250000000000 : ℚ) : ℝ) ≤ stT324 348 := by
  have hc : ((193703/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).1
  have hw2 : ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12979456921/250000000000 : ℚ) : ℝ)
      = ((67007/1250000 : ℚ) : ℝ) * ((193703/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c349 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((97313/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1696293/10000000) (δ := 1637/100000000) (ψ := -72323/62500) 324 302
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t349 : ((104167385487/2500000000000 : ℚ) : ℝ) ≤ stT324 349 := by
  have hc : ((194601/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).1
  have hw2 : ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((535287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104167385487/2500000000000 : ℚ) : ℝ)
      = ((535287/10000000 : ℚ) : ℝ) * ((194601/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c350 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-34743/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 802773/2000000) (δ := 1637/100000000) (ψ := -72323/62500) 324 302
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t350 : ((-18624384889/10000000000000 : ℚ) : ℝ) ≤ stT324 350 := by
  have hc : ((-34843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18624384889/10000000000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-34843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c351 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-409353/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1581219/2500000) (δ := 1637/100000000) (ψ := -72323/62500) 324 302
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t351 : ((-218523354683/5000000000000 : ℚ) : ℝ) ≤ stT324 351 := by
  have hc : ((-409403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218523354683/5000000000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-409403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c352 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-476151/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7078719/10000000) (δ := 8163/500000000) (ψ := -72323/62500) 324 303
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t352 : ((-126908042701/2500000000000 : ℚ) : ℝ) ≤ stT324 352 := by
  have hc : ((-476201/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126908042701/2500000000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-476201/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c353 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-167467/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -478083/1000000) (δ := 8163/500000000) (ψ := -72323/62500) 324 303
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t353 : ((-89160420699/5000000000000 : ℚ) : ℝ) ≤ stT324 353 := by
  have hc : ((-167517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).2
  have h0 : (0:ℝ) ≤ ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89160420699/5000000000000 : ℚ) : ℝ)
      = ((532247/10000000 : ℚ) : ℝ) * ((-167517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c354 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((271929/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2489421/10000000) (δ := 8163/500000000) (ψ := -72323/62500) 324 303
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t354 : ((72251028613/2500000000000 : ℚ) : ℝ) ≤ stT324 354 := by
  have hc : ((271879/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).1
  have hw2 : ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((265747/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72251028613/2500000000000 : ℚ) : ℝ)
      = ((265747/5000000 : ℚ) : ℝ) * ((271879/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c355 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((498327/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -204573/10000000) (δ := 8163/500000000) (ψ := -72323/62500) 324 303
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t355 : ((33057191011/625000000000 : ℚ) : ℝ) ≤ stT324 355 := by
  have hc : ((498277/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).1
  have hw2 : ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66343/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33057191011/625000000000 : ℚ) : ℝ)
      = ((66343/1250000 : ℚ) : ℝ) * ((498277/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c356 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((42199/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2073957/10000000) (δ := 8163/500000000) (ψ := -72323/62500) 324 303
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t356 : ((44724146229/1250000000000 : ℚ) : ℝ) ≤ stT324 356 := by
  have hc : ((168771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).1
  have hw2 : ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((264999/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44724146229/1250000000000 : ℚ) : ℝ)
      = ((264999/5000000 : ℚ) : ℝ) * ((168771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c357 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-166823/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4346007/10000000) (δ := 8163/500000000) (ψ := -72323/62500) 324 303
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t357 : ((-88345166211/10000000000000 : ℚ) : ℝ) ≤ stT324 357 := by
  have hc : ((-166923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).2
  have h0 : (0:ℝ) ≤ ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88345166211/10000000000000 : ℚ) : ℝ)
      = ((529257/10000000 : ℚ) : ℝ) * ((-166923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c358 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-439533/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6611739/10000000) (δ := 8163/500000000) (ψ := -72323/62500) 324 303
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t358 : ((-232327088411/5000000000000 : ℚ) : ℝ) ≤ stT324 358 := by
  have hc : ((-439583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).2
  have h0 : (0:ℝ) ≤ ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232327088411/5000000000000 : ℚ) : ℝ)
      = ((528517/10000000 : ℚ) : ℝ) * ((-439583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c359 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-183673/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -683681/1000000) (δ := 16219/1000000000) (ψ := -72323/62500) 324 304
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t359 : ((-4847474577/100000000000 : ℚ) : ℝ) ≤ stT324 359 := by
  have hc : ((-183693/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).2
  have h0 : (0:ℝ) ≤ ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4847474577/100000000000 : ℚ) : ℝ)
      = ((26389/500000 : ℚ) : ℝ) * ((-183693/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c360 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-259647/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4583633/10000000) (δ := 16219/1000000000) (ψ := -72323/62500) 324 304
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t360 : ((-136898877109/10000000000000 : ℚ) : ℝ) ≤ stT324 360 := by
  have hc : ((-259747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).2
  have h0 : (0:ℝ) ≤ ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136898877109/10000000000000 : ℚ) : ℝ)
      = ((527047/10000000 : ℚ) : ℝ) * ((-259747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c361 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((148513/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1168387/5000000) (δ := 16219/1000000000) (ψ := -72323/62500) 324 304
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t361 : ((1953786543/62500000000 : ℚ) : ℝ) ≤ stT324 361 := by
  have hc : ((18561/31250 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1953786543/62500000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((18561/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c362 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((499631/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -96071/10000000) (δ := 16219/1000000000) (ψ := -72323/62500) 324 304
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t362 : ((65643444657/1250000000000 : ℚ) : ℝ) ≤ stT324 362 := by
  have hc : ((499581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65643444657/1250000000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((499581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c363 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((163987/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 427679/2000000) (δ := 16219/1000000000) (ψ := -72323/62500) 324 304
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t363 : ((43028793603/1250000000000 : ℚ) : ℝ) ≤ stT324 363 := by
  have hc : ((81981/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).1
  have hw2 : ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((524863/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43028793603/1250000000000 : ℚ) : ℝ)
      = ((524863/10000000 : ℚ) : ℝ) * ((81981/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c364 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-8749/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 873341/2000000) (δ := 16219/1000000000) (ψ := -72323/62500) 324 304
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t364 : ((-2294173911/250000000000 : ℚ) : ℝ) ≤ stT324 364 := by
  have hc : ((-4377/25000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2294173911/250000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-4377/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c365 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-437341/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 329447/500000) (δ := 16219/1000000000) (ψ := -72323/62500) 324 304
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t365 : ((-7154404587/156250000000 : ℚ) : ℝ) ≤ stT324 365 := by
  have hc : ((-437391/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7154404587/156250000000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-437391/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c366 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-928499/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6902863/10000000) (δ := 16291/1000000000) (ψ := -72323/62500) 324 305
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t366 : ((-485387054691/10000000000000 : ℚ) : ℝ) ≤ stT324 366 := by
  have hc : ((-928599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-485387054691/10000000000000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-928599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c367 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-301547/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2346389/5000000) (δ := 16291/1000000000) (ψ := -72323/62500) 324 305
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t367 : ((-39364631853/2500000000000 : ℚ) : ℝ) ≤ stT324 367 := by
  have hc : ((-301647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39364631853/2500000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-301647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c368 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((108821/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2488687/10000000) (δ := 16291/1000000000) (ψ := -72323/62500) 324 305
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t368 : ((28358219043/1000000000000 : ℚ) : ℝ) ≤ stT324 368 := by
  have hc : ((108801/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28358219043/1000000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((108801/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c369 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((248313/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29059/1000000) (δ := 16291/1000000000) (ψ := -72323/62500) 324 305
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t369 : ((4039172461/78125000000 : ℚ) : ℝ) ≤ stT324 369 := by
  have hc : ((15518/15625 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4039172461/78125000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((15518/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c370 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((724397/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 950797/5000000) (δ := 16291/1000000000) (ψ := -72323/62500) 324 305
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t370 : ((3012351223/80000000000 : ℚ) : ℝ) ≤ stT324 370 := by
  have hc : ((724297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).1
  have hw2 : ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((4159/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3012351223/80000000000 : ℚ) : ℝ)
      = ((4159/80000 : ℚ) : ℝ) * ((724297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c371 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-64273/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 510973/1250000) (δ := 16291/1000000000) (ψ := -72323/62500) 324 305
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t371 : ((-1336834091/400000000000 : ℚ) : ℝ) ≤ stT324 371 := by
  have hc : ((-64373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1336834091/400000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-64373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c372 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-161093/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3134071/5000000) (δ := 16291/1000000000) (ψ := -72323/62500) 324 305
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t372 : ((-20883305947/500000000000 : ℚ) : ℝ) ≤ stT324 372 := by
  have hc : ((-161113/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20883305947/500000000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-161113/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c373 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-243101/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1453059/2000000) (δ := 8199/500000000) (ψ := -72323/62500) 324 306
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t373 : ((-62943011703/1250000000000 : ℚ) : ℝ) ≤ stT324 373 := by
  have hc : ((-121563/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).2
  have h0 : (0:ℝ) ≤ ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62943011703/1250000000000 : ℚ) : ℝ)
      = ((517781/10000000 : ℚ) : ℝ) * ((-121563/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c374 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-28187/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2548341/5000000) (δ := 8199/500000000) (ψ := -72323/62500) 324 306
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t374 : ((-1822298907/78125000000 : ℚ) : ℝ) ≤ stT324 374 := by
  have hc : ((-112773/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1822298907/78125000000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-112773/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c375 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((386931/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2933739/10000000) (δ := 8199/500000000) (ψ := -72323/62500) 324 306
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t375 : ((199758367907/10000000000000 : ℚ) : ℝ) ≤ stT324 375 := by
  have hc : ((386831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199758367907/10000000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((386831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c376 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((190427/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -194157/2500000) (δ := 8199/500000000) (ψ := -72323/62500) 324 306
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t376 : ((9819479397/200000000000 : ℚ) : ℝ) ≤ stT324 376 := by
  have hc : ((190407/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9819479397/200000000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((190407/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c377 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((852581/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 343683/2500000) (δ := 8199/500000000) (ψ := -72323/62500) 324 306
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t377 : ((219524939753/5000000000000 : ℚ) : ℝ) ≤ stT324 377 := by
  have hc : ((852481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219524939753/5000000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((852481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c378 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((20239/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1760211/5000000) (δ := 8199/500000000) (ψ := -72323/62500) 324 306
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t378 : ((2600844729/312500000000 : ℚ) : ℝ) ≤ stT324 378 := by
  have hc : ((40453/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2600844729/312500000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((40453/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c379 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-319583/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5660523/10000000) (δ := 8199/500000000) (ψ := -72323/62500) 324 306
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t379 : ((-82092302289/2500000000000 : ℚ) : ℝ) ≤ stT324 379 := by
  have hc : ((-319633/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82092302289/2500000000000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-319633/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c380 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-999721/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7794873/10000000) (δ := 8199/500000000) (ψ := -72323/62500) 324 306
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t380 : ((-51289817479/1000000000000 : ℚ) : ℝ) ≤ stT324 380 := by
  have hc : ((-999821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51289817479/1000000000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-999821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c381 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-676453/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -578433/1000000) (δ := 16297/1000000000) (ψ := -72323/62500) 324 307
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t381 : ((-86652231687/2500000000000 : ℚ) : ℝ) ≤ stT324 381 := by
  have hc : ((-676553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86652231687/2500000000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-676553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c382 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((21233/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3661077/10000000) (δ := 16297/1000000000) (ψ := -72323/62500) 324 307
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t382 : ((2713376043/500000000000 : ℚ) : ℝ) ≤ stT324 382 := by
  have hc : ((21213/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2713376043/500000000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((21213/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c383 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((203847/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -771747/5000000) (δ := 16297/1000000000) (ψ := -72323/62500) 324 307
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t383 : ((50853589/1220703125 : ℚ) : ℝ) ≤ stT324 383 := by
  have hc : ((101911/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50853589/1220703125 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((101911/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c384 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((974241/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 284331/5000000) (δ := 16297/1000000000) (ψ := -72323/62500) 324 307
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t384 : ((49711389371/1000000000000 : ℚ) : ℝ) ≤ stT324 384 := by
  have hc : ((974141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).1
  have hw2 : ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49711389371/1000000000000 : ℚ) : ℝ)
      = ((51031/1000000 : ℚ) : ℝ) * ((974141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c385 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((96003/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 267531/1000000) (δ := 16297/1000000000) (ψ := -72323/62500) 324 307
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t385 : ((48917448001/2000000000000 : ℚ) : ℝ) ≤ stT324 385 := by
  have hc : ((95983/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48917448001/2000000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((95983/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c386 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-333283/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 95529/200000) (δ := 16297/1000000000) (ψ := -72323/62500) 324 307
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t386 : ((-169687613021/10000000000000 : ℚ) : ℝ) ≤ stT324 386 := by
  have hc : ((-333383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169687613021/10000000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-333383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c387 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-923869/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6872163/10000000) (δ := 16297/1000000000) (ψ := -72323/62500) 324 307
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t387 : ((-469680237801/10000000000000 : ℚ) : ℝ) ≤ stT324 387 := by
  have hc : ((-923969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-469680237801/10000000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-923969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c388 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-90329/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6745433/10000000) (δ := 16213/1000000000) (ψ := -72323/62500) 324 308
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t388 : ((-22931380743/500000000000 : ℚ) : ℝ) ≤ stT324 388 := by
  have hc : ((-90339/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).2
  have h0 : (0:ℝ) ≤ ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22931380743/500000000000 : ℚ) : ℝ)
      = ((253837/5000000 : ℚ) : ℝ) * ((-90339/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c389 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-289209/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4660493/10000000) (δ := 16213/1000000000) (ψ := -72323/62500) 324 308
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t389 : ((-146685738489/10000000000000 : ℚ) : ℝ) ≤ stT324 389 := by
  have hc : ((-289309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146685738489/10000000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-289309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c390 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((102559/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2580899/10000000) (δ := 16213/1000000000) (ψ := -72323/62500) 324 308
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t390 : ((51922570891/2000000000000 : ℚ) : ℝ) ≤ stT324 390 := by
  have hc : ((102539/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).1
  have hw2 : ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((506369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51922570891/2000000000000 : ℚ) : ℝ)
      = ((506369/10000000 : ℚ) : ℝ) * ((102539/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c391 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((195907/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -506651/10000000) (δ := 16213/1000000000) (ψ := -72323/62500) 324 308
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t391 : ((99064169527/2000000000000 : ℚ) : ℝ) ≤ stT324 391 := by
  have hc : ((195887/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99064169527/2000000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((195887/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c392 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((405501/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 390583/2500000) (δ := 16213/1000000000) (ψ := -72323/62500) 324 308
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t392 : ((51195892319/1250000000000 : ℚ) : ℝ) ≤ stT324 392 := by
  have hc : ((405451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51195892319/1250000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((405451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c393 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((60043/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72521/200000) (δ := 16213/1000000000) (ψ := -72323/62500) 324 308
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t393 : ((30262448969/5000000000000 : ℚ) : ℝ) ≤ stT324 393 := by
  have hc : ((59993/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30262448969/5000000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((59993/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c394 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-646513/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5684503/10000000) (δ := 16213/1000000000) (ψ := -72323/62500) 324 308
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t394 : ((-325759103109/10000000000000 : ℚ) : ℝ) ≤ stT324 394 := by
  have hc : ((-646613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).2
  have h0 : (0:ℝ) ≤ ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-325759103109/10000000000000 : ℚ) : ℝ)
      = ((503793/10000000 : ℚ) : ℝ) * ((-646613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c395 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-499459/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7737691/10000000) (δ := 16213/1000000000) (ψ := -72323/62500) 324 308
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t395 : ((-50266090179/1000000000000 : ℚ) : ℝ) ≤ stT324 395 := by
  have hc : ((-499509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50266090179/1000000000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-499509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c396 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-44751/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5922187/10000000) (δ := 51/3125000) (ψ := -72323/62500) 324 309
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t396 : ((-89965474051/2500000000000 : ℚ) : ℝ) ≤ stT324 396 := by
  have hc : ((-179029/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).2
  have h0 : (0:ℝ) ≤ ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89965474051/2500000000000 : ℚ) : ℝ)
      = ((502519/10000000 : ℚ) : ℝ) * ((-179029/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c397 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((2381/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3879367/10000000) (δ := 51/3125000) (ψ := -72323/62500) 324 309
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t397 : ((475485849/500000000000 : ℚ) : ℝ) ≤ stT324 397 := by
  have hc : ((4737/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).1
  have hw2 : ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((100377/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((475485849/500000000000 : ℚ) : ℝ)
      = ((100377/2000000 : ℚ) : ℝ) * ((4737/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c398 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((370369/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1841569/10000000) (δ := 51/3125000) (ψ := -72323/62500) 324 309
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t398 : ((92811940013/2500000000000 : ℚ) : ℝ) ≤ stT324 398 := by
  have hc : ((370319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).1
  have hw2 : ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250627/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92811940013/2500000000000 : ℚ) : ℝ)
      = ((250627/5000000 : ℚ) : ℝ) * ((370319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c399 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((498541/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38209/2000000) (δ := 51/3125000) (ψ := -72323/62500) 324 309
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t399 : ((124778777683/2500000000000 : ℚ) : ℝ) ≤ stT324 399 := by
  have hc : ((498491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).1
  have hw2 : ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124778777683/2500000000000 : ℚ) : ℝ)
      = ((250313/5000000 : ℚ) : ℝ) * ((498491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c400 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((631413/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 554639/2500000) (δ := 51/3125000) (ψ := -72323/62500) 324 309
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t400 : ((631313/20000000 : ℚ) : ℝ) ≤ stT324 400 := by
  have hc : ((631313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).1
  have hw2 : ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/20 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((631313/20000000 : ℚ) : ℝ)
      = ((1/20 : ℚ) : ℝ) * ((631313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c401 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-31323/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 848209/2000000) (δ := 51/3125000) (ψ := -72323/62500) 324 309
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t401 : ((-3913617549/625000000000 : ℚ) : ℝ) ≤ stT324 401 := by
  have hc : ((-7837/62500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).2
  have h0 : (0:ℝ) ≤ ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3913617549/625000000000 : ℚ) : ℝ)
      = ((499377/10000000 : ℚ) : ℝ) * ((-7837/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c402 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-803157/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6258431/10000000) (δ := 51/3125000) (ψ := -72323/62500) 324 309
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t402 : ((-80125689007/2000000000000 : ℚ) : ℝ) ≤ stT324 402 := by
  have hc : ((-803257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).2
  have h0 : (0:ℝ) ≤ ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80125689007/2000000000000 : ℚ) : ℝ)
      = ((99751/2000000 : ℚ) : ℝ) * ((-803257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c403 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-61633/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -232409/312500) (δ := 2047/125000000) (ψ := -72323/62500) 324 310
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t403 : ((-15352364719/312500000000 : ℚ) : ℝ) ≤ stT324 403 := by
  have hc : ((-246557/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15352364719/312500000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-246557/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c404 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-22621/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1085933/2000000) (δ := 2047/125000000) (ψ := -72323/62500) 324 310
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t404 : ((-90050939/3200000000 : ℚ) : ℝ) ≤ stT324 404 := by
  have hc : ((-181/320 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).2
  have h0 : (0:ℝ) ≤ ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90050939/3200000000 : ℚ) : ℝ)
      = ((497519/10000000 : ℚ) : ℝ) * ((-181/320 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c405 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((99297/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3427183/10000000) (δ := 2047/125000000) (ψ := -72323/62500) 324 310
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t405 : ((49316132041/5000000000000 : ℚ) : ℝ) ≤ stT324 405 := by
  have hc : ((99247/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49316132041/5000000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((99247/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c406 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((420449/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -714821/5000000) (δ := 2047/125000000) (ψ := -72323/62500) 324 310
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t406 : ((208640240109/5000000000000 : ℚ) : ℝ) ≤ stT324 406 := by
  have hc : ((420399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208640240109/5000000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((420399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c407 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((974753/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 281479/5000000) (δ := 2047/125000000) (ψ := -72323/62500) 324 310
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t407 : ((483116973693/10000000000000 : ℚ) : ℝ) ≤ stT324 407 := by
  have hc : ((974653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((483116973693/10000000000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((974653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c408 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((65391/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1275349/5000000) (δ := 2047/125000000) (ψ := -72323/62500) 324 310
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t408 : ((64734260261/2500000000000 : ℚ) : ℝ) ≤ stT324 408 := by
  have hc : ((130757/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64734260261/2500000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((130757/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c409 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-240261/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2266789/5000000) (δ := 2047/125000000) (ψ := -72323/62500) 324 310
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t409 : ((-118851063309/10000000000000 : ℚ) : ℝ) ≤ stT324 409 := by
  have hc : ((-240361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).2
  have h0 : (0:ℝ) ≤ ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118851063309/10000000000000 : ℚ) : ℝ)
      = ((494469/10000000 : ℚ) : ℝ) * ((-240361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c410 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-859271/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3255799/5000000) (δ := 2047/125000000) (ψ := -72323/62500) 324 310
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t410 : ((-84882651783/2000000000000 : ℚ) : ℝ) ≤ stT324 410 := by
  have hc : ((-859371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).2
  have h0 : (0:ℝ) ≤ ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84882651783/2000000000000 : ℚ) : ℝ)
      = ((98773/2000000 : ℚ) : ℝ) * ((-859371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c411 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-96833/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1805781/2500000) (δ := 16269/1000000000) (ψ := -72323/62500) 324 311
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t411 : ((-2985572847/62500000000 : ℚ) : ℝ) ≤ stT324 411 := by
  have hc : ((-96843/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2985572847/62500000000 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-96843/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c412 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-506483/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5254743/10000000) (δ := 16269/1000000000) (ψ := -72323/62500) 324 311
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t412 : ((-49915142739/2000000000000 : ℚ) : ℝ) ≤ stT324 412 := by
  have hc : ((-506583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).2
  have h0 : (0:ℝ) ≤ ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49915142739/2000000000000 : ℚ) : ℝ)
      = ((98533/2000000 : ℚ) : ℝ) * ((-506583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c413 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((251607/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3291141/10000000) (δ := 16269/1000000000) (ψ := -72323/62500) 324 311
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t413 : ((123758294969/10000000000000 : ℚ) : ℝ) ≤ stT324 413 := by
  have hc : ((251507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).1
  have hw2 : ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((492067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123758294969/10000000000000 : ℚ) : ℝ)
      = ((492067/10000000 : ℚ) : ℝ) * ((251507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c414 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((43067/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1332237/10000000) (δ := 16269/1000000000) (ψ := -72323/62500) 324 311
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t414 : ((10581905163/250000000000 : ℚ) : ℝ) ≤ stT324 414 := by
  have hc : ((21531/25000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).1
  have hw2 : ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((491473/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10581905163/250000000000 : ℚ) : ℝ)
      = ((491473/10000000 : ℚ) : ℝ) * ((21531/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c415 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((242303/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 621969/10000000) (δ := 16269/1000000000) (ψ := -72323/62500) 324 311
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t415 : ((92913613/1953125000 : ℚ) : ℝ) ≤ stT324 415 := by
  have hc : ((121139/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).1
  have hw2 : ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((767/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92913613/1953125000 : ℚ) : ℝ)
      = ((767/15625 : ℚ) : ℝ) * ((121139/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c416 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((258027/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 642849/2500000) (δ := 16269/1000000000) (ψ := -72323/62500) 324 311
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t416 : ((12648354333/500000000000 : ℚ) : ℝ) ≤ stT324 416 := by
  have hc : ((257977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).1
  have hw2 : ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12648354333/500000000000 : ℚ) : ℝ)
      = ((49029/1000000 : ℚ) : ℝ) * ((257977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c417 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-23351/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2258103/5000000) (δ := 16269/1000000000) (ψ := -72323/62500) 324 311
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t417 : ((-11439951783/1000000000000 : ℚ) : ℝ) ≤ stT324 417 := by
  have hc : ((-23361/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11439951783/1000000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-23361/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c418 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-847751/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3228159/5000000) (δ := 16269/1000000000) (ψ := -72323/62500) 324 311
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t418 : ((-103674372429/2500000000000 : ℚ) : ℝ) ≤ stT324 418 := by
  have hc : ((-847851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).2
  have h0 : (0:ℝ) ≤ ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103674372429/2500000000000 : ℚ) : ℝ)
      = ((122279/2500000 : ℚ) : ℝ) * ((-847851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c419 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-244237/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -146323/200000) (δ := 8121/500000000) (ψ := -72323/62500) 324 312
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t419 : ((-14916225423/312500000000 : ℚ) : ℝ) ≤ stT324 419 := by
  have hc : ((-122131/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).2
  have h0 : (0:ℝ) ≤ ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14916225423/312500000000 : ℚ) : ℝ)
      = ((122133/2500000 : ℚ) : ℝ) * ((-122131/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c420 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-68849/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -673159/1250000) (δ := 8121/500000000) (ψ := -72323/62500) 324 312
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t420 : ((-67202075573/2500000000000 : ℚ) : ℝ) ≤ stT324 420 := by
  have hc : ((-137723/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).2
  have h0 : (0:ℝ) ≤ ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67202075573/2500000000000 : ℚ) : ℝ)
      = ((487951/10000000 : ℚ) : ℝ) * ((-137723/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c421 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((186101/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3459011/10000000) (δ := 8121/500000000) (ψ := -72323/62500) 324 312
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t421 : ((9065130737/1000000000000 : ℚ) : ℝ) ≤ stT324 421 := by
  have hc : ((186001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9065130737/1000000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((186001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c422 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((816823/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -768643/5000000) (δ := 8121/500000000) (ψ := -72323/62500) 324 312
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t422 : ((49696777827/1250000000000 : ℚ) : ℝ) ≤ stT324 422 := by
  have hc : ((816723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49696777827/1250000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((816723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c423 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((988481/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 189911/5000000) (δ := 8121/500000000) (ψ := -72323/62500) 324 312
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t423 : ((60070832037/1250000000000 : ℚ) : ℝ) ≤ stT324 423 := by
  have hc : ((988381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60070832037/1250000000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((988381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c424 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((152053/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 91699/400000) (δ := 8121/500000000) (ψ := -72323/62500) 324 312
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t424 : ((9228897747/312500000000 : ℚ) : ℝ) ≤ stT324 424 := by
  have hc : ((38007/62500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).1
  have hw2 : ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((242821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9228897747/312500000000 : ℚ) : ℝ)
      = ((242821/5000000 : ℚ) : ℝ) * ((38007/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c425 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-54611/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 262537/625000) (δ := 8121/500000000) (ψ := -72323/62500) 324 312
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t425 : ((-1657157537/312500000000 : ℚ) : ℝ) ≤ stT324 425 := by
  have hc : ((-54661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1657157537/312500000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-54661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c426 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-47807/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3052127/5000000) (δ := 8121/500000000) (ψ := -72323/62500) 324 312
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t426 : ((-46331230503/1250000000000 : ℚ) : ℝ) ≤ stT324 426 := by
  have hc : ((-191253/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46331230503/1250000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-191253/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c427 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-998213/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3852251/5000000) (δ := 16349/1000000000) (ψ := -72323/62500) 324 313
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t427 : ((-241558801671/5000000000000 : ℚ) : ℝ) ≤ stT324 427 := by
  have hc : ((-998313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-241558801671/5000000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-998313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c428 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-68393/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5809831/10000000) (δ := 16349/1000000000) (ψ := -72323/62500) 324 313
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t428 : ((-33063889707/1000000000000 : ℚ) : ℝ) ≤ stT324 428 := by
  have hc : ((-68403/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33063889707/1000000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-68403/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c429 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((603/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3919453/10000000) (δ := 16349/1000000000) (ψ := -72323/62500) 324 313
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t429 : ((70368683/500000000000 : ℚ) : ℝ) ≤ stT324 429 := by
  have hc : ((583/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).1
  have hw2 : ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((120701/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70368683/500000000000 : ℚ) : ℝ)
      = ((120701/2500000 : ℚ) : ℝ) * ((583/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c430 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((687023/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -203353/1000000) (δ := 16349/1000000000) (ψ := -72323/62500) 324 313
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t430 : ((165631560683/5000000000000 : ℚ) : ℝ) ≤ stT324 430 := by
  have hc : ((686923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).1
  have hw2 : ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((241121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165631560683/5000000000000 : ℚ) : ℝ)
      = ((241121/5000000 : ℚ) : ℝ) * ((686923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c431 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((998151/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -76031/5000000) (δ := 16349/1000000000) (ψ := -72323/62500) 324 313
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t431 : ((480744199833/10000000000000 : ℚ) : ℝ) ≤ stT324 431 := by
  have hc : ((998051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((480744199833/10000000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((998051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c432 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((771217/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1725113/10000000) (δ := 16349/1000000000) (ψ := -72323/62500) 324 313
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t432 : ((2968029333/80000000000 : ℚ) : ℝ) ≤ stT324 432 := by
  have hc : ((771117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2968029333/80000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((771117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c433 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((131219/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 719599/2000000) (δ := 16349/1000000000) (ψ := -72323/62500) 324 313
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t433 : ((63011726711/10000000000000 : ℚ) : ℝ) ≤ stT324 433 := by
  have hc : ((131119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63011726711/10000000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((131119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c434 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-36101/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5466503/10000000) (δ := 16349/1000000000) (ψ := -72323/62500) 324 313
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t434 : ((-4333014429/156250000000 : ℚ) : ℝ) ≤ stT324 434 := by
  have hc : ((-144429/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).2
  have h0 : (0:ℝ) ≤ ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4333014429/156250000000 : ℚ) : ℝ)
      = ((30001/625000 : ℚ) : ℝ) * ((-144429/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c435 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-39127/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3665359/5000000) (δ := 16349/1000000000) (ψ := -72323/62500) 324 313
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t435 : ((-2345238223/50000000000 : ℚ) : ℝ) ≤ stT324 435 := by
  have hc : ((-39131/40000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).2
  have h0 : (0:ℝ) ≤ ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2345238223/50000000000 : ℚ) : ℝ)
      = ((59933/1250000 : ℚ) : ℝ) * ((-39131/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c436 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-21511/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1629331/2500000) (δ := 16347/1000000000) (ψ := -72323/62500) 324 314
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t436 : ((-10303116339/250000000000 : ℚ) : ℝ) ≤ stT324 436 := by
  have hc : ((-43027/50000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).2
  have h0 : (0:ℝ) ≤ ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10303116339/250000000000 : ℚ) : ℝ)
      = ((239457/5000000 : ℚ) : ℝ) * ((-43027/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c437 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-28967/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -932339/2000000) (δ := 16347/1000000000) (ψ := -72323/62500) 324 314
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t437 : ((-2772316521/200000000000 : ℚ) : ℝ) ≤ stT324 437 := by
  have hc : ((-28977/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).2
  have h0 : (0:ℝ) ≤ ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2772316521/200000000000 : ℚ) : ℝ)
      = ((95673/2000000 : ℚ) : ℝ) * ((-28977/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c438 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((54001/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2810197/10000000) (δ := 16347/1000000000) (ψ := -72323/62500) 324 314
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t438 : ((25796677093/1250000000000 : ℚ) : ℝ) ≤ stT324 438 := by
  have hc : ((107977/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).1
  have hw2 : ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((238909/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25796677093/1250000000000 : ℚ) : ℝ)
      = ((238909/5000000 : ℚ) : ℝ) * ((107977/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c439 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((37069/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -60187/625000) (δ := 16347/1000000000) (ψ := -72323/62500) 324 314
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t439 : ((3538024749/80000000000 : ℚ) : ℝ) ≤ stT324 439 := by
  have hc : ((7413/8000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).1
  have hw2 : ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((477273/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3538024749/80000000000 : ℚ) : ℝ)
      = ((477273/10000000 : ℚ) : ℝ) * ((7413/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c440 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((187737/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 880001/10000000) (δ := 16347/1000000000) (ψ := -72323/62500) 324 314
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t440 : ((89490513127/2000000000000 : ℚ) : ℝ) ≤ stT324 440 := by
  have hc : ((187717/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).1
  have hw2 : ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89490513127/2000000000000 : ℚ) : ℝ)
      = ((476731/10000000 : ℚ) : ℝ) * ((187717/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c441 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((464689/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1359391/5000000) (δ := 16347/1000000000) (ψ := -72323/62500) 324 314
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t441 : ((22123263591/1000000000000 : ℚ) : ℝ) ≤ stT324 441 := by
  have hc : ((464589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).1
  have hw2 : ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((47619/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22123263591/1000000000000 : ℚ) : ℝ)
      = ((47619/1000000 : ℚ) : ℝ) * ((464589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c442 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-123981/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 569179/1250000) (δ := 16347/1000000000) (ψ := -72323/62500) 324 314
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t442 : ((-14748898303/1250000000000 : ℚ) : ℝ) ≤ stT324 442 := by
  have hc : ((-124031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14748898303/1250000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-124031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c443 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-166409/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6383951/10000000) (δ := 16347/1000000000) (ψ := -72323/62500) 324 314
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t443 : ((-15814582867/400000000000 : ℚ) : ℝ) ≤ stT324 443 := by
  have hc : ((-166429/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).2
  have h0 : (0:ℝ) ≤ ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15814582867/400000000000 : ℚ) : ℝ)
      = ((95023/2000000 : ℚ) : ℝ) * ((-166429/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c444 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-494929/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -937203/1250000) (δ := 203/12500000) (ψ := -72323/62500) 324 315
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t444 : ((-234906638841/5000000000000 : ℚ) : ℝ) ≤ stT324 444 := by
  have hc : ((-494979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234906638841/5000000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-494979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c445 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-643721/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5675367/10000000) (δ := 203/12500000) (ψ := -72323/62500) 324 315
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t445 : ((-152600384883/5000000000000 : ℚ) : ℝ) ≤ stT324 445 := by
  have hc : ((-643821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).2
  have h0 : (0:ℝ) ≤ ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152600384883/5000000000000 : ℚ) : ℝ)
      = ((237023/5000000 : ℚ) : ℝ) * ((-643821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c446 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((27929/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -96429/250000) (δ := 203/12500000) (ψ := -72323/62500) 324 315
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t446 : ((13177393277/10000000000000 : ℚ) : ℝ) ≤ stT324 446 := by
  have hc : ((27829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13177393277/10000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((27829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c447 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((684241/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -510771/2500000) (δ := 203/12500000) (ψ := -72323/62500) 324 315
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t447 : ((323587062603/10000000000000 : ℚ) : ℝ) ≤ stT324 447 := by
  have hc : ((684141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((323587062603/10000000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((684141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c448 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((995661/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -232977/10000000) (δ := 203/12500000) (ψ := -72323/62500) 324 315
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t448 : ((94071554451/2000000000000 : ℚ) : ℝ) ≤ stT324 448 := by
  have hc : ((995561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94071554451/2000000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((995561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c449 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((808499/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1572999/10000000) (δ := 203/12500000) (ψ := -72323/62500) 324 315
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t449 : ((381506931671/10000000000000 : ℚ) : ℝ) ≤ stT324 449 := by
  have hc : ((808399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((381506931671/10000000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((808399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c450 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((54751/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1687503/5000000) (δ := 203/12500000) (ψ := -72323/62500) 324 315
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t450 : ((3224756913/312500000000 : ℚ) : ℝ) ≤ stT324 450 := by
  have hc : ((27363/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).1
  have hw2 : ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3224756913/312500000000 : ℚ) : ℝ)
      = ((117851/2500000 : ℚ) : ℝ) * ((27363/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c451 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-478039/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1293261/2500000) (δ := 203/12500000) (ψ := -72323/62500) 324 315
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t451 : ((-112573524299/5000000000000 : ℚ) : ℝ) ≤ stT324 451 := by
  have hc : ((-478139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112573524299/5000000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-478139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c452 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-937723/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 870879/1250000) (δ := 203/12500000) (ψ := -72323/62500) 324 315
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t452 : ((-441115364103/10000000000000 : ℚ) : ℝ) ≤ stT324 452 := by
  have hc : ((-937823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-441115364103/10000000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-937823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c453 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-233863/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6950831/10000000) (δ := 1627/100000000) (ψ := -72323/62500) 324 316
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t453 : ((-3434067869/78125000000 : ℚ) : ℝ) ≤ stT324 453 := by
  have hc : ((-14618/15625 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3434067869/78125000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-14618/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c454 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-237567/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5164781/10000000) (δ := 1627/100000000) (ψ := -72323/62500) 324 316
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t454 : ((-27879840227/1250000000000 : ℚ) : ℝ) ≤ stT324 454 := by
  have hc : ((-237617/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27879840227/1250000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-237617/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c455 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((3376/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1691269/5000000) (δ := 1627/100000000) (ψ := -72323/62500) 324 316
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t455 : ((25311358737/2500000000000 : ℚ) : ℝ) ≤ stT324 455 := by
  have hc : ((53991/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).1
  have hw2 : ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((468807/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25311358737/2500000000000 : ℚ) : ℝ)
      = ((468807/10000000 : ℚ) : ℝ) * ((53991/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c456 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((200269/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -200533/1250000) (δ := 1627/100000000) (ψ := -72323/62500) 324 316
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t456 : ((5860791453/156250000000 : ℚ) : ℝ) ≤ stT324 456 := by
  have hc : ((50061/62500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).1
  have hw2 : ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117073/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5860791453/156250000000 : ℚ) : ℝ)
      = ((117073/2500000 : ℚ) : ℝ) * ((50061/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c457 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((124711/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 170041/10000000) (δ := 1627/100000000) (ψ := -72323/62500) 324 316
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t457 : ((5833146433/125000000000 : ℚ) : ℝ) ≤ stT324 457 := by
  have hc : ((249397/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).1
  have hw2 : ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((23389/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5833146433/125000000000 : ℚ) : ℝ)
      = ((23389/500000 : ℚ) : ℝ) * ((249397/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c458 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((71357/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1940539/10000000) (δ := 1627/100000000) (ψ := -72323/62500) 324 316
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t458 : ((33338241343/1000000000000 : ℚ) : ℝ) ≤ stT324 458 := by
  have hc : ((71347/100000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).1
  have hw2 : ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((467269/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33338241343/1000000000000 : ℚ) : ℝ)
      = ((467269/10000000 : ℚ) : ℝ) * ((71347/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c459 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((87791/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 370723/1000000) (δ := 1627/100000000) (ψ := -72323/62500) 324 316
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t459 : ((1023266279/250000000000 : ℚ) : ℝ) ≤ stT324 459 := by
  have hc : ((87691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).1
  have hw2 : ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11669/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1023266279/250000000000 : ℚ) : ℝ)
      = ((11669/250000 : ℚ) : ℝ) * ((87691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c460 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-578741/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42734/78125) (δ := 1627/100000000) (ψ := -72323/62500) 324 316
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t460 : ((-269886352773/10000000000000 : ℚ) : ℝ) ≤ stT324 460 := by
  have hc : ((-578841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).2
  have h0 : (0:ℝ) ≤ ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-269886352773/10000000000000 : ℚ) : ℝ)
      = ((466253/10000000 : ℚ) : ℝ) * ((-578841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c461 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-968909/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1807237/2500000) (δ := 1627/100000000) (ψ := -72323/62500) 324 316
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t461 : ((-451313034723/10000000000000 : ℚ) : ℝ) ≤ stT324 461 := by
  have hc : ((-969009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).2
  have h0 : (0:ℝ) ≤ ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-451313034723/10000000000000 : ℚ) : ℝ)
      = ((465747/10000000 : ℚ) : ℝ) * ((-969009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c462 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-449781/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6723907/10000000) (δ := 16377/1000000000) (ψ := -72323/62500) 324 317
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t462 : ((-209280723933/5000000000000 : ℚ) : ℝ) ≤ stT324 462 := by
  have hc : ((-449831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).2
  have h0 : (0:ℝ) ≤ ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209280723933/5000000000000 : ℚ) : ℝ)
      = ((465243/10000000 : ℚ) : ℝ) * ((-449831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c463 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-406129/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -198901/400000) (δ := 16377/1000000000) (ψ := -72323/62500) 324 317
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t463 : ((-9439543273/500000000000 : ℚ) : ℝ) ≤ stT324 463 := by
  have hc : ((-406229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).2
  have h0 : (0:ℝ) ≤ ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9439543273/500000000000 : ℚ) : ℝ)
      = ((23237/500000 : ℚ) : ℝ) * ((-406229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c464 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((13857/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -64499/200000) (δ := 16377/1000000000) (ψ := -72323/62500) 324 317
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t464 : ((803828097/62500000000 : ℚ) : ℝ) ≤ stT324 464 := by
  have hc : ((3463/12500 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((803828097/62500000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((3463/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c465 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((41479/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1481101/10000000) (δ := 16377/1000000000) (ψ := -72323/62500) 324 317
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t465 : ((4808267453/125000000000 : ℚ) : ℝ) ≤ stT324 465 := by
  have hc : ((20737/25000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4808267453/125000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((20737/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c466 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((994641/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 258941/10000000) (δ := 16377/1000000000) (ψ := -72323/62500) 324 317
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t466 : ((460712167381/10000000000000 : ℚ) : ℝ) ≤ stT324 466 := by
  have hc : ((994541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((460712167381/10000000000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((994541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c467 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((349033/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1995257/10000000) (δ := 16377/1000000000) (ψ := -72323/62500) 324 317
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t467 : ((20186223669/625000000000 : ℚ) : ℝ) ≤ stT324 467 := by
  have hc : ((348983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).1
  have hw2 : ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57843/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20186223669/625000000000 : ℚ) : ℝ)
      = ((57843/1250000 : ℚ) : ℝ) * ((348983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c468 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((79573/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3727847/10000000) (δ := 16377/1000000000) (ψ := -72323/62500) 324 317
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t468 : ((146945577/40000000000 : ℚ) : ℝ) ≤ stT324 468 := by
  have hc : ((79473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).1
  have hw2 : ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146945577/40000000000 : ℚ) : ℝ)
      = ((1849/40000 : ℚ) : ℝ) * ((79473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c469 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-574441/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 682099/1250000) (δ := 16377/1000000000) (ψ := -72323/62500) 324 317
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t469 : ((-132649451539/5000000000000 : ℚ) : ℝ) ≤ stT324 469 := by
  have hc : ((-574541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132649451539/5000000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-574541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c470 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-964093/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7182011/10000000) (δ := 16377/1000000000) (ψ := -72323/62500) 324 317
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t470 : ((-222374724169/5000000000000 : ℚ) : ℝ) ≤ stT324 470 := by
  have hc : ((-964193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222374724169/5000000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-964193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c471 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-456577/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6804379/10000000) (δ := 8159/500000000) (ψ := -72323/62500) 324 318
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t471 : ((-26300345319/625000000000 : ℚ) : ℝ) ≤ stT324 471 := by
  have hc : ((-456627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26300345319/625000000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-456627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c472 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-89467/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -101729/200000) (δ := 8159/500000000) (ψ := -72323/62500) 324 318
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t472 : ((-80448813/3906250000 : ℚ) : ℝ) ≤ stT324 472 := by
  have hc : ((-89487/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).2
  have h0 : (0:ℝ) ≤ ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80448813/3906250000 : ℚ) : ℝ)
      = ((3596/78125 : ℚ) : ℝ) * ((-89487/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c473 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((220113/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1686083/5000000) (δ := 8159/500000000) (ψ := -72323/62500) 324 318
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t473 : ((505809887/50000000000 : ℚ) : ℝ) ≤ stT324 473 := by
  have hc : ((220013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((505809887/50000000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((220013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c474 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((787177/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -830723/5000000) (δ := 8159/500000000) (ψ := -72323/62500) 324 318
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t474 : ((72303254451/2000000000000 : ℚ) : ℝ) ≤ stT324 474 := by
  have hc : ((787077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72303254451/2000000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((787077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c475 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((999833/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45629/10000000) (δ := 8159/500000000) (ψ := -72323/62500) 324 318
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t475 : ((458708492123/10000000000000 : ℚ) : ℝ) ≤ stT324 475 := by
  have hc : ((999733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((458708492123/10000000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((999733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c476 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((153017/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1749059/10000000) (δ := 8159/500000000) (ψ := -72323/62500) 324 318
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t476 : ((70126021953/2000000000000 : ℚ) : ℝ) ≤ stT324 476 := by
  have hc : ((152997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70126021953/2000000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((152997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c477 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((190063/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 137957/400000) (δ := 8159/500000000) (ψ := -72323/62500) 324 318
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t477 : ((21744494721/2500000000000 : ℚ) : ℝ) ≤ stT324 477 := by
  have hc : ((189963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21744494721/2500000000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((189963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c478 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-234133/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1286327/2500000) (δ := 8159/500000000) (ψ := -72323/62500) 324 318
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t478 : ((-10711296237/500000000000 : ℚ) : ℝ) ≤ stT324 478 := by
  have hc : ((-234183/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10711296237/500000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-234183/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c479 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-5741/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3419023/5000000) (δ := 8159/500000000) (ψ := -72323/62500) 324 318
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t479 : ((-1311708681/31250000000 : ℚ) : ℝ) ≤ stT324 479 := by
  have hc : ((-45933/50000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1311708681/31250000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-45933/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c480 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-963941/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7180581/10000000) (δ := 16211/1000000000) (ψ := -72323/62500) 324 319
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t480 : ((-110005754469/2500000000000 : ℚ) : ℝ) ≤ stT324 480 := by
  have hc : ((-964041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110005754469/2500000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-964041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c481 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-586847/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -549489/1000000) (δ := 16211/1000000000) (ψ := -72323/62500) 324 319
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t481 : ((-267624941067/10000000000000 : ℚ) : ℝ) ≤ stT324 481 := by
  have hc : ((-586947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-267624941067/10000000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-586947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c482 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((2287/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3812601/10000000) (δ := 16211/1000000000) (ψ := -72323/62500) 324 319
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t482 : ((519710667/250000000000 : ℚ) : ℝ) ≤ stT324 482 := by
  have hc : ((1141/25000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).1
  have hw2 : ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((455487/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((519710667/250000000000 : ℚ) : ℝ)
      = ((455487/10000000 : ℚ) : ℝ) * ((1141/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c483 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((20541/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -533469/2500000) (δ := 16211/1000000000) (ψ := -72323/62500) 324 319
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t483 : ((14952065909/500000000000 : ℚ) : ℝ) ≤ stT324 483 := by
  have hc : ((164303/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14952065909/500000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((164303/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c484 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((39329/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -458553/10000000) (δ := 16211/1000000000) (ψ := -72323/62500) 324 319
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t484 : ((142999857/3200000000 : ℚ) : ℝ) ≤ stT324 484 := by
  have hc : ((1573/1600 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142999857/3200000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((1573/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c485 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((884543/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 606603/5000000) (δ := 16211/1000000000) (ψ := -72323/62500) 324 319
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t485 : ((100401084917/2500000000000 : ℚ) : ℝ) ≤ stT324 485 := by
  have hc : ((884443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100401084917/2500000000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((884443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c486 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((20303/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 720411/2500000) (δ := 16211/1000000000) (ψ := -72323/62500) 324 319
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t486 : ((4603677741/250000000000 : ℚ) : ℝ) ≤ stT324 486 := by
  have hc : ((10149/25000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4603677741/250000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((10149/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c487 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-122657/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4546599/10000000) (δ := 16211/1000000000) (ψ := -72323/62500) 324 319
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t487 : ((-6950492601/625000000000 : ℚ) : ℝ) ≤ stT324 487 := by
  have hc : ((-122707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).2
  have h0 : (0:ℝ) ≤ ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6950492601/625000000000 : ℚ) : ℝ)
      = ((56643/1250000 : ℚ) : ℝ) * ((-122707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c488 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-395507/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 776019/1250000) (δ := 16211/1000000000) (ψ := -72323/62500) 324 319
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t488 : ((-179060347203/5000000000000 : ℚ) : ℝ) ≤ stT324 488 := by
  have hc : ((-395557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179060347203/5000000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-395557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c489 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-249997/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7841741/10000000) (δ := 16299/1000000000) (ψ := -72323/62500) 324 320
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t489 : ((-7066496797/156250000000 : ℚ) : ℝ) ≤ stT324 489 := by
  have hc : ((-125011/125000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7066496797/156250000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-125011/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c490 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-785807/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -386687/625000) (δ := 16299/1000000000) (ψ := -72323/62500) 324 320
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t490 : ((-177518315439/5000000000000 : ℚ) : ℝ) ≤ stT324 490 := by
  have hc : ((-785907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177518315439/5000000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-785907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c491 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-30129/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1133891/2500000) (δ := 16299/1000000000) (ψ := -72323/62500) 324 320
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t491 : ((-13602678101/1250000000000 : ℚ) : ℝ) ≤ stT324 491 := by
  have hc : ((-60283/250000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13602678101/1250000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-60283/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c492 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((80781/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1443769/5000000) (δ := 16299/1000000000) (ψ := -72323/62500) 324 320
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t492 : ((18204902337/1000000000000 : ℚ) : ℝ) ≤ stT324 492 := by
  have hc : ((80761/200000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18204902337/1000000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((80761/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c493 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((439469/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -621457/5000000) (δ := 16299/1000000000) (ψ := -72323/62500) 324 320
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t493 : ((197904210963/5000000000000 : ℚ) : ℝ) ≤ stT324 493 := by
  have hc : ((439419/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197904210963/5000000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((439419/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c494 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((39493/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39847/1000000) (δ := 16299/1000000000) (ψ := -72323/62500) 324 320
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t494 : ((17766930369/400000000000 : ℚ) : ℝ) ≤ stT324 494 := by
  have hc : ((39489/40000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).1
  have hw2 : ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449921/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17766930369/400000000000 : ℚ) : ℝ)
      = ((449921/10000000 : ℚ) : ℝ) * ((39489/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c495 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((686173/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 509113/2500000) (δ := 16299/1000000000) (ψ := -72323/62500) 324 320
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t495 : ((154183243509/5000000000000 : ℚ) : ℝ) ≤ stT324 495 := by
  have hc : ((686073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154183243509/5000000000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((686073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c496 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((5107/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1835597/5000000) (δ := 16299/1000000000) (ψ := -72323/62500) 324 320
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t496 : ((1145432163/250000000000 : ℚ) : ℝ) ≤ stT324 496 := by
  have hc : ((2551/25000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1145432163/250000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((2551/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c497 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-5229/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1060523/2000000) (δ := 16299/1000000000) (ψ := -72323/62500) 324 320
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t497 : ((-117298963/5000000000 : ℚ) : ℝ) ≤ stT324 497 := by
  have hc : ((-523/1000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117298963/5000000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-523/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c498 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-466289/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1386143/2000000) (δ := 16299/1000000000) (ψ := -72323/62500) 324 320
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t498 : ((-208971635629/5000000000000 : ℚ) : ℝ) ≤ stT324 498 := by
  have hc : ((-466339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-208971635629/5000000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-466339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c499 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-960879/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7152389/10000000) (δ := 16397/1000000000) (ψ := -72323/62500) 324 321
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t499 : ((-215096890549/5000000000000 : ℚ) : ℝ) ≤ stT324 499 := by
  have hc : ((-960979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215096890549/5000000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-960979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_c500 :
    |Real.cos (((324 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-598407/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5530769/10000000) (δ := 16397/1000000000) (ψ := -72323/62500) 324 321
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st324_t500 : ((-133830354749/5000000000000 : ℚ) : ℝ) ≤ stT324 500 := by
  have hc : ((-598507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((324 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st324_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).2
  have h0 : (0:ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133830354749/5000000000000 : ℚ) : ℝ)
      = ((223607/5000000 : ℚ) : ℝ) * ((-598507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st324_p1 : ((200917/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT324 (i+1) := by
  rw [Finset.sum_range_one]
  exact st324_t1

theorem st324_p2 : ((2072097211661/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT324 (i+1))
      = (∑ i ∈ Finset.range 1, stT324 (i+1)) + stT324 2 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 1
    simpa using h
  have hprev := st324_p1
  have hstep := st324_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p3 : ((13312269784833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT324 (i+1))
      = (∑ i ∈ Finset.range 2, stT324 (i+1)) + stT324 3 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 2
    simpa using h
  have hprev := st324_p2
  have hstep := st324_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p4 : ((5452917151773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT324 (i+1))
      = (∑ i ∈ Finset.range 3, stT324 (i+1)) + stT324 4 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 3
    simpa using h
  have hprev := st324_p3
  have hstep := st324_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p5 : ((12891234164661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT324 (i+1))
      = (∑ i ∈ Finset.range 4, stT324 (i+1)) + stT324 5 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 4
    simpa using h
  have hprev := st324_p4
  have hstep := st324_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p6 : ((2323426309437/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT324 (i+1))
      = (∑ i ∈ Finset.range 5, stT324 (i+1)) + stT324 6 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 5
    simpa using h
  have hprev := st324_p5
  have hstep := st324_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p7 : ((696176169891/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT324 (i+1))
      = (∑ i ∈ Finset.range 6, stT324 (i+1)) + stT324 7 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 6
    simpa using h
  have hprev := st324_p6
  have hstep := st324_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p8 : ((636976661847/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT324 (i+1))
      = (∑ i ∈ Finset.range 7, stT324 (i+1)) + stT324 8 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 7
    simpa using h
  have hprev := st324_p7
  have hstep := st324_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p9 : ((-15482347007/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT324 (i+1))
      = (∑ i ∈ Finset.range 8, stT324 (i+1)) + stT324 9 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 8
    simpa using h
  have hprev := st324_p8
  have hstep := st324_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p10 : ((39882798709/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT324 (i+1))
      = (∑ i ∈ Finset.range 9, stT324 (i+1)) + stT324 10 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 9
    simpa using h
  have hprev := st324_p9
  have hstep := st324_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p11 : ((3520803206531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT324 (i+1))
      = (∑ i ∈ Finset.range 10, stT324 (i+1)) + stT324 11 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 10
    simpa using h
  have hprev := st324_p10
  have hstep := st324_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p12 : ((2269020936771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT324 (i+1))
      = (∑ i ∈ Finset.range 11, stT324 (i+1)) + stT324 12 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 11
    simpa using h
  have hprev := st324_p11
  have hstep := st324_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p13 : ((-2834601927/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT324 (i+1))
      = (∑ i ∈ Finset.range 12, stT324 (i+1)) + stT324 13 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 12
    simpa using h
  have hprev := st324_p12
  have hstep := st324_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p14 : ((-43974868413/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT324 (i+1))
      = (∑ i ∈ Finset.range 13, stT324 (i+1)) + stT324 14 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 13
    simpa using h
  have hprev := st324_p13
  have hstep := st324_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p15 : ((127995995469/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT324 (i+1))
      = (∑ i ∈ Finset.range 14, stT324 (i+1)) + stT324 15 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 14
    simpa using h
  have hprev := st324_p14
  have hstep := st324_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p16 : ((475852245469/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT324 (i+1))
      = (∑ i ∈ Finset.range 15, stT324 (i+1)) + stT324 16 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 15
    simpa using h
  have hprev := st324_p15
  have hstep := st324_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p17 : ((707759658521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT324 (i+1))
      = (∑ i ∈ Finset.range 16, stT324 (i+1)) + stT324 17 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 16
    simpa using h
  have hprev := st324_p16
  have hstep := st324_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p18 : ((171567192661/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT324 (i+1))
      = (∑ i ∈ Finset.range 17, stT324 (i+1)) + stT324 18 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 17
    simpa using h
  have hprev := st324_p17
  have hstep := st324_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p19 : ((3995423914807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT324 (i+1))
      = (∑ i ∈ Finset.range 18, stT324 (i+1)) + stT324 19 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 18
    simpa using h
  have hprev := st324_p18
  have hstep := st324_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p20 : ((2829278675719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT324 (i+1))
      = (∑ i ∈ Finset.range 19, stT324 (i+1)) + stT324 20 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 19
    simpa using h
  have hprev := st324_p19
  have hstep := st324_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p21 : ((755036165369/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT324 (i+1))
      = (∑ i ∈ Finset.range 20, stT324 (i+1)) + stT324 21 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 20
    simpa using h
  have hprev := st324_p20
  have hstep := st324_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p22 : ((1890690427613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT324 (i+1))
      = (∑ i ∈ Finset.range 21, stT324 (i+1)) + stT324 22 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 21
    simpa using h
  have hprev := st324_p21
  have hstep := st324_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p23 : ((3314968888253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT324 (i+1))
      = (∑ i ∈ Finset.range 22, stT324 (i+1)) + stT324 23 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 22
    simpa using h
  have hprev := st324_p22
  have hstep := st324_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p24 : ((64893700353/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT324 (i+1))
      = (∑ i ∈ Finset.range 23, stT324 (i+1)) + stT324 24 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 23
    simpa using h
  have hprev := st324_p23
  have hstep := st324_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p25 : ((77021675353/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT324 (i+1))
      = (∑ i ∈ Finset.range 24, stT324 (i+1)) + stT324 25 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 24
    simpa using h
  have hprev := st324_p24
  have hstep := st324_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p26 : ((26806441441/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT324 (i+1))
      = (∑ i ∈ Finset.range 25, stT324 (i+1)) + stT324 26 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 25
    simpa using h
  have hprev := st324_p25
  have hstep := st324_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p27 : ((2026979512849/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT324 (i+1))
      = (∑ i ∈ Finset.range 26, stT324 (i+1)) + stT324 27 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 26
    simpa using h
  have hprev := st324_p26
  have hstep := st324_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p28 : ((624434724401/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT324 (i+1))
      = (∑ i ∈ Finset.range 27, stT324 (i+1)) + stT324 28 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 27
    simpa using h
  have hprev := st324_p27
  have hstep := st324_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p29 : ((10811125306691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT324 (i+1))
      = (∑ i ∈ Finset.range 28, stT324 (i+1)) + stT324 29 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 28
    simpa using h
  have hprev := st324_p28
  have hstep := st324_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p30 : ((9163864193127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT324 (i+1))
      = (∑ i ∈ Finset.range 29, stT324 (i+1)) + stT324 30 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 29
    simpa using h
  have hprev := st324_p29
  have hstep := st324_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p31 : ((1806021332717/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT324 (i+1))
      = (∑ i ∈ Finset.range 30, stT324 (i+1)) + stT324 31 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 30
    simpa using h
  have hprev := st324_p30
  have hstep := st324_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p32 : ((10453575486361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT324 (i+1))
      = (∑ i ∈ Finset.range 31, stT324 (i+1)) + stT324 32 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 31
    simpa using h
  have hprev := st324_p31
  have hstep := st324_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p33 : ((8719566627337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT324 (i+1))
      = (∑ i ∈ Finset.range 32, stT324 (i+1)) + stT324 33 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 32
    simpa using h
  have hprev := st324_p32
  have hstep := st324_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p34 : ((2603236990323/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT324 (i+1))
      = (∑ i ∈ Finset.range 33, stT324 (i+1)) + stT324 34 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 33
    simpa using h
  have hprev := st324_p33
  have hstep := st324_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p35 : ((1091968624737/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT324 (i+1))
      = (∑ i ∈ Finset.range 34, stT324 (i+1)) + stT324 35 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 34
    simpa using h
  have hprev := st324_p34
  have hstep := st324_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p36 : ((1037766334113/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT324 (i+1))
      = (∑ i ∈ Finset.range 35, stT324 (i+1)) + stT324 36 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 35
    simpa using h
  have hprev := st324_p35
  have hstep := st324_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p37 : ((228524255491/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT324 (i+1))
      = (∑ i ∈ Finset.range 36, stT324 (i+1)) + stT324 37 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 36
    simpa using h
  have hprev := st324_p36
  have hstep := st324_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p38 : ((4624739245943/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT324 (i+1))
      = (∑ i ∈ Finset.range 37, stT324 (i+1)) + stT324 38 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 37
    simpa using h
  have hprev := st324_p37
  have hstep := st324_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p39 : ((2636006927803/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT324 (i+1))
      = (∑ i ∈ Finset.range 38, stT324 (i+1)) + stT324 39 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 38
    simpa using h
  have hprev := st324_p38
  have hstep := st324_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p40 : ((72128200509/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT324 (i+1))
      = (∑ i ∈ Finset.range 39, stT324 (i+1)) + stT324 40 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 39
    simpa using h
  have hprev := st324_p39
  have hstep := st324_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p41 : ((21395502809/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT324 (i+1))
      = (∑ i ∈ Finset.range 40, stT324 (i+1)) + stT324 41 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 40
    simpa using h
  have hprev := st324_p40
  have hstep := st324_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p42 : ((619850053271/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT324 (i+1))
      = (∑ i ∈ Finset.range 41, stT324 (i+1)) + stT324 42 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 41
    simpa using h
  have hprev := st324_p41
  have hstep := st324_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p43 : ((5463062641163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT324 (i+1))
      = (∑ i ∈ Finset.range 42, stT324 (i+1)) + stT324 43 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 42
    simpa using h
  have hprev := st324_p42
  have hstep := st324_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p44 : ((2570047091191/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT324 (i+1))
      = (∑ i ∈ Finset.range 43, stT324 (i+1)) + stT324 44 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 43
    simpa using h
  have hprev := st324_p43
  have hstep := st324_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p45 : ((88019282821/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT324 (i+1))
      = (∑ i ∈ Finset.range 44, stT324 (i+1)) + stT324 45 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 44
    simpa using h
  have hprev := st324_p44
  have hstep := st324_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p46 : ((76815902451/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT324 (i+1))
      = (∑ i ∈ Finset.range 45, stT324 (i+1)) + stT324 46 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 45
    simpa using h
  have hprev := st324_p45
  have hstep := st324_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p47 : ((7423067871/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT324 (i+1))
      = (∑ i ∈ Finset.range 46, stT324 (i+1)) + stT324 47 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 46
    simpa using h
  have hprev := st324_p46
  have hstep := st324_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p48 : ((63451569573/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT324 (i+1))
      = (∑ i ∈ Finset.range 47, stT324 (i+1)) + stT324 48 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 47
    simpa using h
  have hprev := st324_p47
  have hstep := st324_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p49 : ((8912863045057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT324 (i+1))
      = (∑ i ∈ Finset.range 48, stT324 (i+1)) + stT324 49 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 48
    simpa using h
  have hprev := st324_p48
  have hstep := st324_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p50 : ((10117783834761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT324 (i+1))
      = (∑ i ∈ Finset.range 49, stT324 (i+1)) + stT324 50 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 49
    simpa using h
  have hprev := st324_p49
  have hstep := st324_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p51 : ((11397397506321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT324 (i+1))
      = (∑ i ∈ Finset.range 50, stT324 (i+1)) + stT324 51 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 50
    simpa using h
  have hprev := st324_p50
  have hstep := st324_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p52 : ((12669263589321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT324 (i+1))
      = (∑ i ∈ Finset.range 51, stT324 (i+1)) + stT324 52 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 51
    simpa using h
  have hprev := st324_p51
  have hstep := st324_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p53 : ((13860327473661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT324 (i+1))
      = (∑ i ∈ Finset.range 52, stT324 (i+1)) + stT324 53 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 52
    simpa using h
  have hprev := st324_p52
  have hstep := st324_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p54 : ((1857198300819/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT324 (i+1))
      = (∑ i ∈ Finset.range 53, stT324 (i+1)) + stT324 54 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 53
    simpa using h
  have hprev := st324_p53
  have hstep := st324_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p55 : ((3097109051929/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT324 (i+1))
      = (∑ i ∈ Finset.range 54, stT324 (i+1)) + stT324 55 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 54
    simpa using h
  have hprev := st324_p54
  have hstep := st324_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p56 : ((3107597717723/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT324 (i+1))
      = (∑ i ∈ Finset.range 55, stT324 (i+1)) + stT324 56 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 55
    simpa using h
  have hprev := st324_p55
  have hstep := st324_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p57 : ((14892220471663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT324 (i+1))
      = (∑ i ∈ Finset.range 56, stT324 (i+1)) + stT324 57 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 56
    simpa using h
  have hprev := st324_p56
  have hstep := st324_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p58 : ((213900512837/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT324 (i+1))
      = (∑ i ∈ Finset.range 57, stT324 (i+1)) + stT324 58 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 57
    simpa using h
  have hprev := st324_p57
  have hstep := st324_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p59 : ((6229184526089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT324 (i+1))
      = (∑ i ∈ Finset.range 58, stT324 (i+1)) + stT324 59 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 58
    simpa using h
  have hprev := st324_p58
  have hstep := st324_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p60 : ((11953237565543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT324 (i+1))
      = (∑ i ∈ Finset.range 59, stT324 (i+1)) + stT324 60 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 59
    simpa using h
  have hprev := st324_p59
  have hstep := st324_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p61 : ((12595717265367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT324 (i+1))
      = (∑ i ∈ Finset.range 60, stT324 (i+1)) + stT324 61 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 60
    simpa using h
  have hprev := st324_p60
  have hstep := st324_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p62 : ((1386501087481/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT324 (i+1))
      = (∑ i ∈ Finset.range 61, stT324 (i+1)) + stT324 62 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 61
    simpa using h
  have hprev := st324_p61
  have hstep := st324_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p63 : ((14471077889741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT324 (i+1))
      = (∑ i ∈ Finset.range 62, stT324 (i+1)) + stT324 63 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 62
    simpa using h
  have hprev := st324_p62
  have hstep := st324_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p64 : ((6843079255903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT324 (i+1))
      = (∑ i ∈ Finset.range 63, stT324 (i+1)) + stT324 64 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 63
    simpa using h
  have hprev := st324_p63
  have hstep := st324_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p65 : ((250572769411/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT324 (i+1))
      = (∑ i ∈ Finset.range 64, stT324 (i+1)) + stT324 65 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 64
    simpa using h
  have hprev := st324_p64
  have hstep := st324_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p66 : ((3173093354979/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT324 (i+1))
      = (∑ i ∈ Finset.range 65, stT324 (i+1)) + stT324 66 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 65
    simpa using h
  have hprev := st324_p65
  have hstep := st324_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p67 : ((3478380025251/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT324 (i+1))
      = (∑ i ∈ Finset.range 66, stT324 (i+1)) + stT324 67 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 66
    simpa using h
  have hprev := st324_p66
  have hstep := st324_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p68 : ((7025719591311/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT324 (i+1))
      = (∑ i ∈ Finset.range 67, stT324 (i+1)) + stT324 68 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 67
    simpa using h
  have hprev := st324_p67
  have hstep := st324_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p69 : ((6428942607831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT324 (i+1))
      = (∑ i ∈ Finset.range 68, stT324 (i+1)) + stT324 69 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 68
    simpa using h
  have hprev := st324_p68
  have hstep := st324_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p70 : ((12760759711893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT324 (i+1))
      = (∑ i ∈ Finset.range 69, stT324 (i+1)) + stT324 70 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 69
    simpa using h
  have hprev := st324_p69
  have hstep := st324_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p71 : ((13946681482449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT324 (i+1))
      = (∑ i ∈ Finset.range 70, stT324 (i+1)) + stT324 71 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 70
    simpa using h
  have hprev := st324_p70
  have hstep := st324_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p72 : ((547751996521/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT324 (i+1))
      = (∑ i ∈ Finset.range 71, stT324 (i+1)) + stT324 72 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 71
    simpa using h
  have hprev := st324_p71
  have hstep := st324_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p73 : ((12644681219821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT324 (i+1))
      = (∑ i ∈ Finset.range 72, stT324 (i+1)) + stT324 73 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 72
    simpa using h
  have hprev := st324_p72
  have hstep := st324_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p74 : ((13448524074013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT324 (i+1))
      = (∑ i ∈ Finset.range 73, stT324 (i+1)) + stT324 74 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 73
    simpa using h
  have hprev := st324_p73
  have hstep := st324_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p75 : ((13944209071213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT324 (i+1))
      = (∑ i ∈ Finset.range 74, stT324 (i+1)) + stT324 75 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 74
    simpa using h
  have hprev := st324_p74
  have hstep := st324_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p76 : ((3199328687733/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT324 (i+1))
      = (∑ i ∈ Finset.range 75, stT324 (i+1)) + stT324 76 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 75
    simpa using h
  have hprev := st324_p75
  have hstep := st324_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p77 : ((6648583008411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT324 (i+1))
      = (∑ i ∈ Finset.range 76, stT324 (i+1)) + stT324 77 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 76
    simpa using h
  have hprev := st324_p76
  have hstep := st324_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p78 : ((13922236137841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT324 (i+1))
      = (∑ i ∈ Finset.range 77, stT324 (i+1)) + stT324 78 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 77
    simpa using h
  have hprev := st324_p77
  have hstep := st324_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p79 : ((12797035629041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT324 (i+1))
      = (∑ i ∈ Finset.range 78, stT324 (i+1)) + stT324 79 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 78
    simpa using h
  have hprev := st324_p78
  have hstep := st324_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p80 : ((13461800162313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT324 (i+1))
      = (∑ i ∈ Finset.range 79, stT324 (i+1)) + stT324 80 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 79
    simpa using h
  have hprev := st324_p79
  have hstep := st324_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p81 : ((13732731246331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT324 (i+1))
      = (∑ i ∈ Finset.range 80, stT324 (i+1)) + stT324 81 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 80
    simpa using h
  have hprev := st324_p80
  have hstep := st324_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p82 : ((12758481584811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT324 (i+1))
      = (∑ i ∈ Finset.range 81, stT324 (i+1)) + stT324 82 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 81
    simpa using h
  have hprev := st324_p81
  have hstep := st324_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p83 : ((13808505679567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT324 (i+1))
      = (∑ i ∈ Finset.range 82, stT324 (i+1)) + stT324 83 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 82
    simpa using h
  have hprev := st324_p82
  have hstep := st324_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p84 : ((13250400051487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT324 (i+1))
      = (∑ i ∈ Finset.range 83, stT324 (i+1)) + stT324 84 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 83
    simpa using h
  have hprev := st324_p83
  have hstep := st324_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p85 : ((13081834128757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT324 (i+1))
      = (∑ i ∈ Finset.range 84, stT324 (i+1)) + stT324 85 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 84
    simpa using h
  have hprev := st324_p84
  have hstep := st324_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p86 : ((6929079738751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT324 (i+1))
      = (∑ i ∈ Finset.range 85, stT324 (i+1)) + stT324 86 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 85
    simpa using h
  have hprev := st324_p85
  have hstep := st324_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p87 : ((12800115816401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT324 (i+1))
      = (∑ i ∈ Finset.range 86, stT324 (i+1)) + stT324 87 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 86
    simpa using h
  have hprev := st324_p86
  have hstep := st324_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p88 : ((1378248341903/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT324 (i+1))
      = (∑ i ∈ Finset.range 87, stT324 (i+1)) + stT324 88 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 87
    simpa using h
  have hprev := st324_p87
  have hstep := st324_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p89 : ((1642309806767/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT324 (i+1))
      = (∑ i ∈ Finset.range 88, stT324 (i+1)) + stT324 89 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 88
    simpa using h
  have hprev := st324_p88
  have hstep := st324_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p90 : ((333029131171/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT324 (i+1))
      = (∑ i ∈ Finset.range 89, stT324 (i+1)) + stT324 90 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 89
    simpa using h
  have hprev := st324_p89
  have hstep := st324_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p91 : ((3398718311881/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT324 (i+1))
      = (∑ i ∈ Finset.range 90, stT324 (i+1)) + stT324 91 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 90
    simpa using h
  have hprev := st324_p90
  have hstep := st324_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p92 : ((1619064875059/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT324 (i+1))
      = (∑ i ∈ Finset.range 91, stT324 (i+1)) + stT324 92 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 91
    simpa using h
  have hprev := st324_p91
  have hstep := st324_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p93 : ((2767723495969/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT324 (i+1))
      = (∑ i ∈ Finset.range 92, stT324 (i+1)) + stT324 93 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 92
    simpa using h
  have hprev := st324_p92
  have hstep := st324_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p94 : ((12832469444533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT324 (i+1))
      = (∑ i ∈ Finset.range 93, stT324 (i+1)) + stT324 94 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 93
    simpa using h
  have hprev := st324_p93
  have hstep := st324_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p95 : ((13856196448801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT324 (i+1))
      = (∑ i ∈ Finset.range 94, stT324 (i+1)) + stT324 95 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 94
    simpa using h
  have hprev := st324_p94
  have hstep := st324_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p96 : ((6442977160991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT324 (i+1))
      = (∑ i ∈ Finset.range 95, stT324 (i+1)) + stT324 96 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 95
    simpa using h
  have hprev := st324_p95
  have hstep := st324_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p97 : ((6880491783083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT324 (i+1))
      = (∑ i ∈ Finset.range 96, stT324 (i+1)) + stT324 97 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 96
    simpa using h
  have hprev := st324_p96
  have hstep := st324_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p98 : ((12996995760889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT324 (i+1))
      = (∑ i ∈ Finset.range 97, stT324 (i+1)) + stT324 98 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 97
    simpa using h
  have hprev := st324_p97
  have hstep := st324_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p99 : ((6825897226009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT324 (i+1))
      = (∑ i ∈ Finset.range 98, stT324 (i+1)) + stT324 99 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 98
    simpa using h
  have hprev := st324_p98
  have hstep := st324_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p100 : ((6545588726009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT324 (i+1))
      = (∑ i ∈ Finset.range 99, stT324 (i+1)) + stT324 100 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 99
    simpa using h
  have hprev := st324_p99
  have hstep := st324_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p101 : ((6789575778557/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT324 (i+1))
      = (∑ i ∈ Finset.range 100, stT324 (i+1)) + stT324 101 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 100
    simpa using h
  have hprev := st324_p100
  have hstep := st324_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p102 : ((1313759703681/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT324 (i+1))
      = (∑ i ∈ Finset.range 101, stT324 (i+1)) + stT324 102 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 101
    simpa using h
  have hprev := st324_p101
  have hstep := st324_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p103 : ((3389906810529/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT324 (i+1))
      = (∑ i ∈ Finset.range 102, stT324 (i+1)) + stT324 103 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 102
    simpa using h
  have hprev := st324_p102
  have hstep := st324_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p104 : ((2625918492797/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT324 (i+1))
      = (∑ i ∈ Finset.range 103, stT324 (i+1)) + stT324 104 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 103
    simpa using h
  have hprev := st324_p103
  have hstep := st324_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p105 : ((2718606937457/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT324 (i+1))
      = (∑ i ∈ Finset.range 104, stT324 (i+1)) + stT324 105 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 104
    simpa using h
  have hprev := st324_p104
  have hstep := st324_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p106 : ((13072533204031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT324 (i+1))
      = (∑ i ∈ Finset.range 105, stT324 (i+1)) + stT324 106 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 105
    simpa using h
  have hprev := st324_p105
  have hstep := st324_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p107 : ((546750859959/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT324 (i+1))
      = (∑ i ∈ Finset.range 106, stT324 (i+1)) + stT324 107 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 106
    simpa using h
  have hprev := st324_p106
  have hstep := st324_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p108 : ((811471493851/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT324 (i+1))
      = (∑ i ∈ Finset.range 107, stT324 (i+1)) + stT324 108 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 107
    simpa using h
  have hprev := st324_p107
  have hstep := st324_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p109 : ((860082121177/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT324 (i+1))
      = (∑ i ∈ Finset.range 108, stT324 (i+1)) + stT324 109 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 108
    simpa using h
  have hprev := st324_p108
  have hstep := st324_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p110 : ((1612339972073/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT324 (i+1))
      = (∑ i ∈ Finset.range 109, stT324 (i+1)) + stT324 110 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 109
    simpa using h
  have hprev := st324_p109
  have hstep := st324_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p111 : ((863911477553/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT324 (i+1))
      = (∑ i ∈ Finset.range 110, stT324 (i+1)) + stT324 111 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 110
    simpa using h
  have hprev := st324_p110
  have hstep := st324_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p112 : ((804849280537/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT324 (i+1))
      = (∑ i ∈ Finset.range 111, stT324 (i+1)) + stT324 112 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 111
    simpa using h
  have hprev := st324_p111
  have hstep := st324_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p113 : ((26923895081/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT324 (i+1))
      = (∑ i ∈ Finset.range 112, stT324 (i+1)) + stT324 113 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 112
    simpa using h
  have hprev := st324_p112
  have hstep := st324_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p114 : ((6494059270947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT324 (i+1))
      = (∑ i ∈ Finset.range 113, stT324 (i+1)) + stT324 114 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 113
    simpa using h
  have hprev := st324_p113
  have hstep := st324_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p115 : ((6796365877699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT324 (i+1))
      = (∑ i ∈ Finset.range 114, stT324 (i+1)) + stT324 115 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 114
    simpa using h
  have hprev := st324_p114
  have hstep := st324_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p116 : ((13257597053771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT324 (i+1))
      = (∑ i ∈ Finset.range 115, stT324 (i+1)) + stT324 116 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 115
    simpa using h
  have hprev := st324_p115
  have hstep := st324_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p117 : ((13265583809271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT324 (i+1))
      = (∑ i ∈ Finset.range 116, stT324 (i+1)) + stT324 117 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 116
    simpa using h
  have hprev := st324_p116
  have hstep := st324_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p118 : ((13603004559213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT324 (i+1))
      = (∑ i ∈ Finset.range 117, stT324 (i+1)) + stT324 118 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 117
    simpa using h
  have hprev := st324_p117
  have hstep := st324_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p119 : ((12956388918787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT324 (i+1))
      = (∑ i ∈ Finset.range 118, stT324 (i+1)) + stT324 119 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 118
    simpa using h
  have hprev := st324_p118
  have hstep := st324_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p120 : ((13811379309307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT324 (i+1))
      = (∑ i ∈ Finset.range 119, stT324 (i+1)) + stT324 120 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 119
    simpa using h
  have hprev := st324_p119
  have hstep := st324_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p121 : ((1613287743259/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT324 (i+1))
      = (∑ i ∈ Finset.range 120, stT324 (i+1)) + stT324 121 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 120
    simpa using h
  have hprev := st324_p120
  have hstep := st324_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p122 : ((6834223882549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT324 (i+1))
      = (∑ i ∈ Finset.range 121, stT324 (i+1)) + stT324 122 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 121
    simpa using h
  have hprev := st324_p121
  have hstep := st324_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p123 : ((103381232731/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT324 (i+1))
      = (∑ i ∈ Finset.range 122, stT324 (i+1)) + stT324 123 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 122
    simpa using h
  have hprev := st324_p122
  have hstep := st324_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p124 : ((1322017691811/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT324 (i+1))
      = (∑ i ∈ Finset.range 123, stT324 (i+1)) + stT324 124 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 123
    simpa using h
  have hprev := st324_p123
  have hstep := st324_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p125 : ((1368996575559/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT324 (i+1))
      = (∑ i ∈ Finset.range 124, stT324 (i+1)) + stT324 125 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 124
    simpa using h
  have hprev := st324_p124
  have hstep := st324_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p126 : ((12890735982747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT324 (i+1))
      = (∑ i ∈ Finset.range 125, stT324 (i+1)) + stT324 126 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 125
    simpa using h
  have hprev := st324_p125
  have hstep := st324_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p127 : ((13771348077147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT324 (i+1))
      = (∑ i ∈ Finset.range 126, stT324 (i+1)) + stT324 127 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 126
    simpa using h
  have hprev := st324_p126
  have hstep := st324_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p128 : ((13108473084159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT324 (i+1))
      = (∑ i ∈ Finset.range 127, stT324 (i+1)) + stT324 128 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 127
    simpa using h
  have hprev := st324_p127
  have hstep := st324_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p129 : ((13307123734959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT324 (i+1))
      = (∑ i ∈ Finset.range 128, stT324 (i+1)) + stT324 129 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 128
    simpa using h
  have hprev := st324_p128
  have hstep := st324_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p130 : ((13658230224693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT324 (i+1))
      = (∑ i ∈ Finset.range 129, stT324 (i+1)) + stT324 130 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 129
    simpa using h
  have hprev := st324_p129
  have hstep := st324_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p131 : ((12891396820293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT324 (i+1))
      = (∑ i ∈ Finset.range 130, stT324 (i+1)) + stT324 131 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 130
    simpa using h
  have hprev := st324_p130
  have hstep := st324_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p132 : ((13747991781657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT324 (i+1))
      = (∑ i ∈ Finset.range 131, stT324 (i+1)) + stT324 132 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 131
    simpa using h
  have hprev := st324_p131
  have hstep := st324_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p133 : ((13191423354397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT324 (i+1))
      = (∑ i ∈ Finset.range 132, stT324 (i+1)) + stT324 133 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 132
    simpa using h
  have hprev := st324_p132
  have hstep := st324_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p134 : ((13175941094179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT324 (i+1))
      = (∑ i ∈ Finset.range 133, stT324 (i+1)) + stT324 134 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 133
    simpa using h
  have hprev := st324_p133
  have hstep := st324_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p135 : ((13762825651317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT324 (i+1))
      = (∑ i ∈ Finset.range 134, stT324 (i+1)) + stT324 135 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 134
    simpa using h
  have hprev := st324_p134
  have hstep := st324_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p136 : ((3226834581861/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT324 (i+1))
      = (∑ i ∈ Finset.range 135, stT324 (i+1)) + stT324 136 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 135
    simpa using h
  have hprev := st324_p135
  have hstep := st324_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p137 : ((108494090123/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT324 (i+1))
      = (∑ i ∈ Finset.range 136, stT324 (i+1)) + stT324 137 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 136
    simpa using h
  have hprev := st324_p136
  have hstep := st324_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p138 : ((134872975593/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT324 (i+1))
      = (∑ i ∈ Finset.range 137, stT324 (i+1)) + stT324 138 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 137
    simpa using h
  have hprev := st324_p137
  have hstep := st324_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p139 : ((12931298643343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT324 (i+1))
      = (∑ i ∈ Finset.range 138, stT324 (i+1)) + stT324 139 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 138
    simpa using h
  have hprev := st324_p138
  have hstep := st324_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p140 : ((2755157501429/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT324 (i+1))
      = (∑ i ∈ Finset.range 139, stT324 (i+1)) + stT324 140 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 139
    simpa using h
  have hprev := st324_p139
  have hstep := st324_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p141 : ((13188056363561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT324 (i+1))
      = (∑ i ∈ Finset.range 140, stT324 (i+1)) + stT324 141 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 140
    simpa using h
  have hprev := st324_p140
  have hstep := st324_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p142 : ((13121319575829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT324 (i+1))
      = (∑ i ∈ Finset.range 141, stT324 (i+1)) + stT324 142 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 141
    simpa using h
  have hprev := st324_p141
  have hstep := st324_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p143 : ((13800181667671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT324 (i+1))
      = (∑ i ∈ Finset.range 142, stT324 (i+1)) + stT324 143 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 142
    simpa using h
  have hprev := st324_p142
  have hstep := st324_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p144 : ((12994851856741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT324 (i+1))
      = (∑ i ∈ Finset.range 143, stT324 (i+1)) + stT324 144 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 143
    simpa using h
  have hprev := st324_p143
  have hstep := st324_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p145 : ((13326614077471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT324 (i+1))
      = (∑ i ∈ Finset.range 144, stT324 (i+1)) + stT324 145 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 144
    simpa using h
  have hprev := st324_p144
  have hstep := st324_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p146 : ((6862994469753/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT324 (i+1))
      = (∑ i ∈ Finset.range 145, stT324 (i+1)) + stT324 146 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 145
    simpa using h
  have hprev := st324_p145
  have hstep := st324_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p147 : ((12908858437227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT324 (i+1))
      = (∑ i ∈ Finset.range 146, stT324 (i+1)) + stT324 147 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 146
    simpa using h
  have hprev := st324_p146
  have hstep := st324_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p148 : ((13476805327599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT324 (i+1))
      = (∑ i ∈ Finset.range 147, stT324 (i+1)) + stT324 148 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 147
    simpa using h
  have hprev := st324_p147
  have hstep := st324_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p149 : ((13636925665011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT324 (i+1))
      = (∑ i ∈ Finset.range 148, stT324 (i+1)) + stT324 149 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 148
    simpa using h
  have hprev := st324_p148
  have hstep := st324_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p150 : ((12884669015977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT324 (i+1))
      = (∑ i ∈ Finset.range 149, stT324 (i+1)) + stT324 150 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 149
    simpa using h
  have hprev := st324_p149
  have hstep := st324_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p151 : ((13561179118257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT324 (i+1))
      = (∑ i ∈ Finset.range 150, stT324 (i+1)) + stT324 151 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 150
    simpa using h
  have hprev := st324_p150
  have hstep := st324_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p152 : ((6789196621059/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT324 (i+1))
      = (∑ i ∈ Finset.range 151, stT324 (i+1)) + stT324 152 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 151
    simpa using h
  have hprev := st324_p151
  have hstep := st324_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p153 : ((6440894048881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT324 (i+1))
      = (∑ i ∈ Finset.range 152, stT324 (i+1)) + stT324 153 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 152
    simpa using h
  have hprev := st324_p152
  have hstep := st324_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p154 : ((3397379547881/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT324 (i+1))
      = (∑ i ∈ Finset.range 153, stT324 (i+1)) + stT324 154 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 153
    simpa using h
  have hprev := st324_p153
  have hstep := st324_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p155 : ((211984348631/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT324 (i+1))
      = (∑ i ∈ Finset.range 154, stT324 (i+1)) + stT324 155 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 154
    simpa using h
  have hprev := st324_p154
  have hstep := st324_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p156 : ((3220128176541/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT324 (i+1))
      = (∑ i ∈ Finset.range 155, stT324 (i+1)) + stT324 156 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 155
    simpa using h
  have hprev := st324_p155
  have hstep := st324_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p157 : ((6784404204701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT324 (i+1))
      = (∑ i ∈ Finset.range 156, stT324 (i+1)) + stT324 157 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 156
    simpa using h
  have hprev := st324_p156
  have hstep := st324_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p158 : ((13603878948633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT324 (i+1))
      = (∑ i ∈ Finset.range 157, stT324 (i+1)) + stT324 158 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 157
    simpa using h
  have hprev := st324_p157
  have hstep := st324_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p159 : ((103061394301/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT324 (i+1))
      = (∑ i ∈ Finset.range 158, stT324 (i+1)) + stT324 159 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 158
    simpa using h
  have hprev := st324_p158
  have hstep := st324_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p160 : ((6748397700973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT324 (i+1))
      = (∑ i ∈ Finset.range 159, stT324 (i+1)) + stT324 160 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 159
    simpa using h
  have hprev := st324_p159
  have hstep := st324_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p161 : ((6839409431883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT324 (i+1))
      = (∑ i ∈ Finset.range 160, stT324 (i+1)) + stT324 161 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 160
    simpa using h
  have hprev := st324_p160
  have hstep := st324_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p162 : ((12909078138441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT324 (i+1))
      = (∑ i ∈ Finset.range 161, stT324 (i+1)) + stT324 162 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 161
    simpa using h
  have hprev := st324_p161
  have hstep := st324_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p163 : ((13367479486921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT324 (i+1))
      = (∑ i ∈ Finset.range 162, stT324 (i+1)) + stT324 163 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 162
    simpa using h
  have hprev := st324_p162
  have hstep := st324_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p164 : ((13765273948689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT324 (i+1))
      = (∑ i ∈ Finset.range 163, stT324 (i+1)) + stT324 164 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 163
    simpa using h
  have hprev := st324_p163
  have hstep := st324_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p165 : ((6496933926539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT324 (i+1))
      = (∑ i ∈ Finset.range 164, stT324 (i+1)) + stT324 165 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 164
    simpa using h
  have hprev := st324_p164
  have hstep := st324_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p166 : ((3296655206207/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT324 (i+1))
      = (∑ i ∈ Finset.range 165, stT324 (i+1)) + stT324 166 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 165
    simpa using h
  have hprev := st324_p165
  have hstep := st324_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p167 : ((2762703455599/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT324 (i+1))
      = (∑ i ∈ Finset.range 166, stT324 (i+1)) + stT324 167 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 166
    simpa using h
  have hprev := st324_p166
  have hstep := st324_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p168 : ((2633705813199/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT324 (i+1))
      = (∑ i ∈ Finset.range 167, stT324 (i+1)) + stT324 168 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 167
    simpa using h
  have hprev := st324_p167
  have hstep := st324_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p169 : ((12993873628983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT324 (i+1))
      = (∑ i ∈ Finset.range 168, stT324 (i+1)) + stT324 169 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 168
    simpa using h
  have hprev := st324_p168
  have hstep := st324_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p170 : ((13755975844187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT324 (i+1))
      = (∑ i ∈ Finset.range 169, stT324 (i+1)) + stT324 170 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 169
    simpa using h
  have hprev := st324_p169
  have hstep := st324_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p171 : ((13429306578187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT324 (i+1))
      = (∑ i ∈ Finset.range 170, stT324 (i+1)) + stT324 171 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 170
    simpa using h
  have hprev := st324_p170
  have hstep := st324_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p172 : ((3219093716707/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT324 (i+1))
      = (∑ i ∈ Finset.range 171, stT324 (i+1)) + stT324 172 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 171
    simpa using h
  have hprev := st324_p171
  have hstep := st324_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p173 : ((13542172407313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT324 (i+1))
      = (∑ i ∈ Finset.range 172, stT324 (i+1)) + stT324 173 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 172
    simpa using h
  have hprev := st324_p172
  have hstep := st324_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p174 : ((547916763713/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT324 (i+1))
      = (∑ i ∈ Finset.range 173, stT324 (i+1)) + stT324 174 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 173
    simpa using h
  have hprev := st324_p173
  have hstep := st324_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p175 : ((6472133853451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT324 (i+1))
      = (∑ i ∈ Finset.range 174, stT324 (i+1)) + stT324 175 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 174
    simpa using h
  have hprev := st324_p174
  have hstep := st324_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p176 : ((6602847250209/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT324 (i+1))
      = (∑ i ∈ Finset.range 175, stT324 (i+1)) + stT324 176 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 175
    simpa using h
  have hprev := st324_p175
  have hstep := st324_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p177 : ((345442812113/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT324 (i+1))
      = (∑ i ∈ Finset.range 176, stT324 (i+1)) + stT324 177 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 176
    simpa using h
  have hprev := st324_p176
  have hstep := st324_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p178 : ((3310733280197/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT324 (i+1))
      = (∑ i ∈ Finset.range 177, stT324 (i+1)) + stT324 178 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 177
    simpa using h
  have hprev := st324_p177
  have hstep := st324_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p179 : ((403623298967/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT324 (i+1))
      = (∑ i ∈ Finset.range 178, stT324 (i+1)) + stT324 179 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 178
    simpa using h
  have hprev := st324_p178
  have hstep := st324_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p180 : ((13643508197739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT324 (i+1))
      = (∑ i ∈ Finset.range 179, stT324 (i+1)) + stT324 180 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 179
    simpa using h
  have hprev := st324_p179
  have hstep := st324_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p181 : ((13639156948809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT324 (i+1))
      = (∑ i ∈ Finset.range 180, stT324 (i+1)) + stT324 181 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 180
    simpa using h
  have hprev := st324_p180
  have hstep := st324_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p182 : ((12915709550059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT324 (i+1))
      = (∑ i ∈ Finset.range 181, stT324 (i+1)) + stT324 182 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 181
    simpa using h
  have hprev := st324_p181
  have hstep := st324_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p183 : ((6610091056601/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT324 (i+1))
      = (∑ i ∈ Finset.range 182, stT324 (i+1)) + stT324 183 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 182
    simpa using h
  have hprev := st324_p182
  have hstep := st324_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p184 : ((2764063926441/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT324 (i+1))
      = (∑ i ∈ Finset.range 183, stT324 (i+1)) + stT324 184 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 183
    simpa using h
  have hprev := st324_p183
  have hstep := st324_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p185 : ((1329037298413/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT324 (i+1))
      = (∑ i ∈ Finset.range 184, stT324 (i+1)) + stT324 185 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 184
    simpa using h
  have hprev := st324_p184
  have hstep := st324_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p186 : ((6441130946063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT324 (i+1))
      = (∑ i ∈ Finset.range 185, stT324 (i+1)) + stT324 186 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 185
    simpa using h
  have hprev := st324_p185
  have hstep := st324_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p187 : ((6774404138067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT324 (i+1))
      = (∑ i ∈ Finset.range 186, stT324 (i+1)) + stT324 187 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 186
    simpa using h
  have hprev := st324_p186
  have hstep := st324_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p188 : ((6870393022341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT324 (i+1))
      = (∑ i ∈ Finset.range 187, stT324 (i+1)) + stT324 188 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 187
    simpa using h
  have hprev := st324_p187
  have hstep := st324_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p189 : ((13018414238561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT324 (i+1))
      = (∑ i ∈ Finset.range 188, stT324 (i+1)) + stT324 189 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 188
    simpa using h
  have hprev := st324_p188
  have hstep := st324_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p190 : ((13033240791573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT324 (i+1))
      = (∑ i ∈ Finset.range 189, stT324 (i+1)) + stT324 190 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 189
    simpa using h
  have hprev := st324_p189
  have hstep := st324_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p191 : ((13748558088659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT324 (i+1))
      = (∑ i ∈ Finset.range 190, stT324 (i+1)) + stT324 191 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 190
    simpa using h
  have hprev := st324_p190
  have hstep := st324_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p192 : ((542193761563/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT324 (i+1))
      = (∑ i ∈ Finset.range 191, stT324 (i+1)) + stT324 192 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 191
    simpa using h
  have hprev := st324_p191
  have hstep := st324_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p193 : ((12887368739699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT324 (i+1))
      = (∑ i ∈ Finset.range 192, stT324 (i+1)) + stT324 193 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 192
    simpa using h
  have hprev := st324_p192
  have hstep := st324_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p194 : ((13223666010563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT324 (i+1))
      = (∑ i ∈ Finset.range 193, stT324 (i+1)) + stT324 194 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 193
    simpa using h
  have hprev := st324_p193
  have hstep := st324_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p195 : ((13821567492013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT324 (i+1))
      = (∑ i ∈ Finset.range 194, stT324 (i+1)) + stT324 195 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 194
    simpa using h
  have hprev := st324_p194
  have hstep := st324_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p196 : ((13378430171901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT324 (i+1))
      = (∑ i ∈ Finset.range 195, stT324 (i+1)) + stT324 196 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 195
    simpa using h
  have hprev := st324_p195
  have hstep := st324_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p197 : ((12855687349317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT324 (i+1))
      = (∑ i ∈ Finset.range 196, stT324 (i+1)) + stT324 197 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 196
    simpa using h
  have hprev := st324_p196
  have hstep := st324_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p198 : ((334342829287/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT324 (i+1))
      = (∑ i ∈ Finset.range 197, stT324 (i+1)) + stT324 198 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 197
    simpa using h
  have hprev := st324_p197
  have hstep := st324_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p199 : ((6913103754581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT324 (i+1))
      = (∑ i ∈ Finset.range 198, stT324 (i+1)) + stT324 199 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 198
    simpa using h
  have hprev := st324_p198
  have hstep := st324_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p200 : ((1657328534577/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT324 (i+1))
      = (∑ i ∈ Finset.range 199, stT324 (i+1)) + stT324 200 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 199
    simpa using h
  have hprev := st324_p199
  have hstep := st324_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p201 : ((6431893083003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT324 (i+1))
      = (∑ i ∈ Finset.range 200, stT324 (i+1)) + stT324 201 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 200
    simpa using h
  have hprev := st324_p200
  have hstep := st324_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p202 : ((6730501056997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT324 (i+1))
      = (∑ i ∈ Finset.range 201, stT324 (i+1)) + stT324 202 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 201
    simpa using h
  have hprev := st324_p201
  have hstep := st324_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p203 : ((6907168846603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT324 (i+1))
      = (∑ i ∈ Finset.range 202, stT324 (i+1)) + stT324 203 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 202
    simpa using h
  have hprev := st324_p202
  have hstep := st324_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p204 : ((6600987385329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT324 (i+1))
      = (∑ i ∈ Finset.range 203, stT324 (i+1)) + stT324 204 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 203
    simpa using h
  have hprev := st324_p203
  have hstep := st324_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p205 : ((12871498872819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT324 (i+1))
      = (∑ i ∈ Finset.range 204, stT324 (i+1)) + stT324 205 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 204
    simpa using h
  have hprev := st324_p204
  have hstep := st324_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p206 : ((6743593596763/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT324 (i+1))
      = (∑ i ∈ Finset.range 205, stT324 (i+1)) + stT324 206 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 205
    simpa using h
  have hprev := st324_p205
  have hstep := st324_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p207 : ((6906717887123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT324 (i+1))
      = (∑ i ∈ Finset.range 206, stT324 (i+1)) + stT324 207 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 206
    simpa using h
  have hprev := st324_p206
  have hstep := st324_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p208 : ((6602113303379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT324 (i+1))
      = (∑ i ∈ Finset.range 207, stT324 (i+1)) + stT324 208 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 207
    simpa using h
  have hprev := st324_p207
  have hstep := st324_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p209 : ((12863534142663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT324 (i+1))
      = (∑ i ∈ Finset.range 208, stT324 (i+1)) + stT324 209 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 208
    simpa using h
  have hprev := st324_p208
  have hstep := st324_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p210 : ((6727823933119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT324 (i+1))
      = (∑ i ∈ Finset.range 209, stT324 (i+1)) + stT324 210 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 209
    simpa using h
  have hprev := st324_p209
  have hstep := st324_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p211 : ((6913750436791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT324 (i+1))
      = (∑ i ∈ Finset.range 210, stT324 (i+1)) + stT324 211 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 210
    simpa using h
  have hprev := st324_p210
  have hstep := st324_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p212 : ((13264347825293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT324 (i+1))
      = (∑ i ∈ Finset.range 211, stT324 (i+1)) + stT324 212 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 211
    simpa using h
  have hprev := st324_p211
  have hstep := st324_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p213 : ((2569300899787/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT324 (i+1))
      = (∑ i ∈ Finset.range 212, stT324 (i+1)) + stT324 213 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 212
    simpa using h
  have hprev := st324_p212
  have hstep := st324_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p214 : ((106922567239/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT324 (i+1))
      = (∑ i ∈ Finset.range 213, stT324 (i+1)) + stT324 214 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 213
    simpa using h
  have hprev := st324_p213
  have hstep := st324_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p215 : ((13839635455983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT324 (i+1))
      = (∑ i ∈ Finset.range 214, stT324 (i+1)) + stT324 215 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 214
    simpa using h
  have hprev := st324_p214
  have hstep := st324_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p216 : ((2676732971853/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT324 (i+1))
      = (∑ i ∈ Finset.range 215, stT324 (i+1)) + stT324 216 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 215
    simpa using h
  have hprev := st324_p215
  have hstep := st324_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p217 : ((2569461884953/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT324 (i+1))
      = (∑ i ∈ Finset.range 216, stT324 (i+1)) + stT324 217 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 216
    simpa using h
  have hprev := st324_p216
  have hstep := st324_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p218 : ((2643551174759/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT324 (i+1))
      = (∑ i ∈ Finset.range 217, stT324 (i+1)) + stT324 218 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 217
    simpa using h
  have hprev := st324_p217
  have hstep := st324_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p219 : ((3453406710507/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT324 (i+1))
      = (∑ i ∈ Finset.range 218, stT324 (i+1)) + stT324 219 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 218
    simpa using h
  have hprev := st324_p218
  have hstep := st324_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p220 : ((3388346579057/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT324 (i+1))
      = (∑ i ∈ Finset.range 219, stT324 (i+1)) + stT324 220 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 219
    simpa using h
  have hprev := st324_p219
  have hstep := st324_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p221 : ((12909663144129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT324 (i+1))
      = (∑ i ∈ Finset.range 220, stT324 (i+1)) + stT324 221 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 220
    simpa using h
  have hprev := st324_p220
  have hstep := st324_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p222 : ((13034190770681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT324 (i+1))
      = (∑ i ∈ Finset.range 221, stT324 (i+1)) + stT324 222 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 221
    simpa using h
  have hprev := st324_p221
  have hstep := st324_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p223 : ((1370203238803/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT324 (i+1))
      = (∑ i ∈ Finset.range 222, stT324 (i+1)) + stT324 223 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 222
    simpa using h
  have hprev := st324_p222
  have hstep := st324_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p224 : ((13734697720047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT324 (i+1))
      = (∑ i ∈ Finset.range 223, stT324 (i+1)) + stT324 224 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 223
    simpa using h
  have hprev := st324_p223
  have hstep := st324_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p225 : ((13078330725197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT324 (i+1))
      = (∑ i ∈ Finset.range 224, stT324 (i+1)) + stT324 225 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 224
    simpa using h
  have hprev := st324_p224
  have hstep := st324_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p226 : ((6437486594507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT324 (i+1))
      = (∑ i ∈ Finset.range 225, stT324 (i+1)) + stT324 226 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 225
    simpa using h
  have hprev := st324_p225
  have hstep := st324_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p227 : ((3368073339439/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT324 (i+1))
      = (∑ i ∈ Finset.range 226, stT324 (i+1)) + stT324 227 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 226
    simpa using h
  have hprev := st324_p226
  have hstep := st324_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p228 : ((6922407997979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT324 (i+1))
      = (∑ i ∈ Finset.range 227, stT324 (i+1)) + stT324 228 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 227
    simpa using h
  have hprev := st324_p227
  have hstep := st324_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p229 : ((13361401125517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT324 (i+1))
      = (∑ i ∈ Finset.range 228, stT324 (i+1)) + stT324 229 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 228
    simpa using h
  have hprev := st324_p228
  have hstep := st324_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p230 : ((12840995221363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT324 (i+1))
      = (∑ i ∈ Finset.range 229, stT324 (i+1)) + stT324 230 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 229
    simpa using h
  have hprev := st324_p229
  have hstep := st324_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p231 : ((13154197004089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT324 (i+1))
      = (∑ i ∈ Finset.range 230, stT324 (i+1)) + stT324 231 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 230
    simpa using h
  have hprev := st324_p230
  have hstep := st324_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p232 : ((13776294557221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT324 (i+1))
      = (∑ i ∈ Finset.range 231, stT324 (i+1)) + stT324 232 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 231
    simpa using h
  have hprev := st324_p231
  have hstep := st324_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p233 : ((13679781329059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT324 (i+1))
      = (∑ i ∈ Finset.range 232, stT324 (i+1)) + stT324 233 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 232
    simpa using h
  have hprev := st324_p232
  have hstep := st324_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p234 : ((13026405493747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT324 (i+1))
      = (∑ i ∈ Finset.range 233, stT324 (i+1)) + stT324 234 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 233
    simpa using h
  have hprev := st324_p233
  have hstep := st324_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p235 : ((3220268115877/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT324 (i+1))
      = (∑ i ∈ Finset.range 234, stT324 (i+1)) + stT324 235 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 234
    simpa using h
  have hprev := st324_p234
  have hstep := st324_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p236 : ((3368872935317/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT324 (i+1))
      = (∑ i ∈ Finset.range 235, stT324 (i+1)) + stT324 236 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 235
    simpa using h
  have hprev := st324_p235
  have hstep := st324_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p237 : ((1385305891907/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT324 (i+1))
      = (∑ i ∈ Finset.range 236, stT324 (i+1)) + stT324 237 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 236
    simpa using h
  have hprev := st324_p236
  have hstep := st324_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p238 : ((6707049853849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT324 (i+1))
      = (∑ i ∈ Finset.range 237, stT324 (i+1)) + stT324 238 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 237
    simpa using h
  have hprev := st324_p237
  have hstep := st324_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p239 : ((12856425094577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT324 (i+1))
      = (∑ i ∈ Finset.range 238, stT324 (i+1)) + stT324 239 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 238
    simpa using h
  have hprev := st324_p238
  have hstep := st324_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p240 : ((13055451184587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT324 (i+1))
      = (∑ i ∈ Finset.range 239, stT324 (i+1)) + stT324 240 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 239
    simpa using h
  have hprev := st324_p239
  have hstep := st324_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p241 : ((2739387818087/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT324 (i+1))
      = (∑ i ∈ Finset.range 240, stT324 (i+1)) + stT324 241 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 240
    simpa using h
  have hprev := st324_p240
  have hstep := st324_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p242 : ((2757218470199/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT324 (i+1))
      = (∑ i ∈ Finset.range 241, stT324 (i+1)) + stT324 242 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 241
    simpa using h
  have hprev := st324_p241
  have hstep := st324_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p243 : ((6594430988253/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT324 (i+1))
      = (∑ i ∈ Finset.range 242, stT324 (i+1)) + stT324 243 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 242
    simpa using h
  have hprev := st324_p242
  have hstep := st324_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p244 : ((6409941194583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT324 (i+1))
      = (∑ i ∈ Finset.range 243, stT324 (i+1)) + stT324 244 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 243
    simpa using h
  have hprev := st324_p243
  have hstep := st324_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p245 : ((6618370336889/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT324 (i+1))
      = (∑ i ∈ Finset.range 244, stT324 (i+1)) + stT324 245 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 244
    simpa using h
  have hprev := st324_p244
  have hstep := st324_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p246 : ((6903994502461/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT324 (i+1))
      = (∑ i ∈ Finset.range 245, stT324 (i+1)) + stT324 246 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 245
    simpa using h
  have hprev := st324_p245
  have hstep := st324_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p247 : ((13679289546827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT324 (i+1))
      = (∑ i ∈ Finset.range 246, stT324 (i+1)) + stT324 247 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 246
    simpa using h
  have hprev := st324_p246
  have hstep := st324_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p248 : ((1630662195427/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT324 (i+1))
      = (∑ i ∈ Finset.range 247, stT324 (i+1)) + stT324 248 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 247
    simpa using h
  have hprev := st324_p247
  have hstep := st324_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p249 : ((12842805315341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT324 (i+1))
      = (∑ i ∈ Finset.range 248, stT324 (i+1)) + stT324 249 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 248
    simpa using h
  have hprev := st324_p248
  have hstep := st324_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p250 : ((6682846589343/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT324 (i+1))
      = (∑ i ∈ Finset.range 249, stT324 (i+1)) + stT324 250 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 249
    simpa using h
  have hprev := st324_p249
  have hstep := st324_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p251 : ((6924985862817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT324 (i+1))
      = (∑ i ∈ Finset.range 250, stT324 (i+1)) + stT324 251 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 250
    simpa using h
  have hprev := st324_p250
  have hstep := st324_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p252 : ((3399186695643/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT324 (i+1))
      = (∑ i ∈ Finset.range 251, stT324 (i+1)) + stT324 252 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 251
    simpa using h
  have hprev := st324_p251
  have hstep := st324_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p253 : ((12972968806167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT324 (i+1))
      = (∑ i ∈ Finset.range 252, stT324 (i+1)) + stT324 253 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 252
    simpa using h
  have hprev := st324_p252
  have hstep := st324_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p254 : ((12868770325527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT324 (i+1))
      = (∑ i ∈ Finset.range 253, stT324 (i+1)) + stT324 254 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 253
    simpa using h
  have hprev := st324_p253
  have hstep := st324_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p255 : ((13428597673479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT324 (i+1))
      = (∑ i ∈ Finset.range 254, stT324 (i+1)) + stT324 255 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 254
    simpa using h
  have hprev := st324_p254
  have hstep := st324_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p256 : ((13862331423479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT324 (i+1))
      = (∑ i ∈ Finset.range 255, stT324 (i+1)) + stT324 256 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 255
    simpa using h
  have hprev := st324_p255
  have hstep := st324_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p257 : ((13565395744687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT324 (i+1))
      = (∑ i ∈ Finset.range 256, stT324 (i+1)) + stT324 257 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 256
    simpa using h
  have hprev := st324_p256
  have hstep := st324_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p258 : ((12953209752619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT324 (i+1))
      = (∑ i ∈ Finset.range 257, stT324 (i+1)) + stT324 258 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 257
    simpa using h
  have hprev := st324_p257
  have hstep := st324_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p259 : ((12870176079519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT324 (i+1))
      = (∑ i ∈ Finset.range 258, stT324 (i+1)) + stT324 259 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 258
    simpa using h
  have hprev := st324_p258
  have hstep := st324_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p260 : ((13426874372969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT324 (i+1))
      = (∑ i ∈ Finset.range 259, stT324 (i+1)) + stT324 260 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 259
    simpa using h
  have hprev := st324_p259
  have hstep := st324_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p261 : ((13863530445929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT324 (i+1))
      = (∑ i ∈ Finset.range 260, stT324 (i+1)) + stT324 261 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 260
    simpa using h
  have hprev := st324_p260
  have hstep := st324_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p262 : ((6795755583613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT324 (i+1))
      = (∑ i ∈ Finset.range 261, stT324 (i+1)) + stT324 262 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 261
    simpa using h
  have hprev := st324_p261
  have hstep := st324_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p263 : ((6489602744621/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT324 (i+1))
      = (∑ i ∈ Finset.range 262, stT324 (i+1)) + stT324 263 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 262
    simpa using h
  have hprev := st324_p262
  have hstep := st324_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p264 : ((1284370379413/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT324 (i+1))
      = (∑ i ∈ Finset.range 263, stT324 (i+1)) + stT324 264 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 263
    simpa using h
  have hprev := st324_p263
  have hstep := st324_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p265 : ((1336156922221/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT324 (i+1))
      = (∑ i ∈ Finset.range 264, stT324 (i+1)) + stT324 265 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 264
    simpa using h
  have hprev := st324_p264
  have hstep := st324_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p266 : ((13848645004393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT324 (i+1))
      = (∑ i ∈ Finset.range 265, stT324 (i+1)) + stT324 266 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 265
    simpa using h
  have hprev := st324_p265
  have hstep := st324_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p267 : ((13669151716039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT324 (i+1))
      = (∑ i ∈ Finset.range 266, stT324 (i+1)) + stT324 267 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 266
    simpa using h
  have hprev := st324_p266
  have hstep := st324_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p268 : ((13059417291943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT324 (i+1))
      = (∑ i ∈ Finset.range 267, stT324 (i+1)) + stT324 268 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 267
    simpa using h
  have hprev := st324_p267
  have hstep := st324_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p269 : ((12807342034369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT324 (i+1))
      = (∑ i ∈ Finset.range 268, stT324 (i+1)) + stT324 269 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 268
    simpa using h
  have hprev := st324_p268
  have hstep := st324_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p270 : ((13233601812229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT324 (i+1))
      = (∑ i ∈ Finset.range 269, stT324 (i+1)) + stT324 270 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 269
    simpa using h
  have hprev := st324_p269
  have hstep := st324_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p271 : ((110338432009/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT324 (i+1))
      = (∑ i ∈ Finset.range 270, stT324 (i+1)) + stT324 271 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 270
    simpa using h
  have hprev := st324_p270
  have hstep := st324_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p272 : ((2755334632453/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT324 (i+1))
      = (∑ i ∈ Finset.range 271, stT324 (i+1)) + stT324 272 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 271
    simpa using h
  have hprev := st324_p271
  have hstep := st324_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p273 : ((13209360880781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT324 (i+1))
      = (∑ i ∈ Finset.range 272, stT324 (i+1)) + stT324 273 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 272
    simpa using h
  have hprev := st324_p272
  have hstep := st324_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p274 : ((3200235730627/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT324 (i+1))
      = (∑ i ∈ Finset.range 273, stT324 (i+1)) + stT324 274 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 273
    simpa using h
  have hprev := st324_p273
  have hstep := st324_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p275 : ((408020826939/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT324 (i+1))
      = (∑ i ∈ Finset.range 274, stT324 (i+1)) + stT324 275 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 274
    simpa using h
  have hprev := st324_p274
  have hstep := st324_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p276 : ((546318850467/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT324 (i+1))
      = (∑ i ∈ Finset.range 275, stT324 (i+1)) + stT324 276 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 275
    simpa using h
  have hprev := st324_p275
  have hstep := st324_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p277 : ((3466785359541/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT324 (i+1))
      = (∑ i ∈ Finset.range 276, stT324 (i+1)) + stT324 277 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 276
    simpa using h
  have hprev := st324_p276
  have hstep := st324_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p278 : ((6715951638559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT324 (i+1))
      = (∑ i ∈ Finset.range 277, stT324 (i+1)) + stT324 278 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 277
    simpa using h
  have hprev := st324_p277
  have hstep := st324_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p279 : ((1610182389631/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT324 (i+1))
      = (∑ i ∈ Finset.range 278, stT324 (i+1)) + stT324 279 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 278
    simpa using h
  have hprev := st324_p278
  have hstep := st324_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p280 : ((12877148520053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT324 (i+1))
      = (∑ i ∈ Finset.range 279, stT324 (i+1)) + stT324 280 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 279
    simpa using h
  have hprev := st324_p279
  have hstep := st324_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p281 : ((41940923809/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT324 (i+1))
      = (∑ i ∈ Finset.range 280, stT324 (i+1)) + stT324 281 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 280
    simpa using h
  have hprev := st324_p280
  have hstep := st324_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p282 : ((13865523057491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT324 (i+1))
      = (∑ i ∈ Finset.range 281, stT324 (i+1)) + stT324 282 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 281
    simpa using h
  have hprev := st324_p281
  have hstep := st324_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p283 : ((13687395844507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT324 (i+1))
      = (∑ i ∈ Finset.range 282, stT324 (i+1)) + stT324 283 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 282
    simpa using h
  have hprev := st324_p282
  have hstep := st324_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p284 : ((13098479012647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT324 (i+1))
      = (∑ i ∈ Finset.range 283, stT324 (i+1)) + stT324 284 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 283
    simpa using h
  have hprev := st324_p283
  have hstep := st324_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p285 : ((6392976359251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT324 (i+1))
      = (∑ i ∈ Finset.range 284, stT324 (i+1)) + stT324 285 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 284
    simpa using h
  have hprev := st324_p284
  have hstep := st324_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p286 : ((6554778835747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT324 (i+1))
      = (∑ i ∈ Finset.range 285, stT324 (i+1)) + stT324 286 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 285
    simpa using h
  have hprev := st324_p285
  have hstep := st324_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p287 : ((6847030500533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT324 (i+1))
      = (∑ i ∈ Finset.range 286, stT324 (i+1)) + stT324 287 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 286
    simpa using h
  have hprev := st324_p286
  have hstep := st324_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p288 : ((3467674903849/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT324 (i+1))
      = (∑ i ∈ Finset.range 287, stT324 (i+1)) + stT324 288 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 287
    simpa using h
  have hprev := st324_p287
  have hstep := st324_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p289 : ((420036203491/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT324 (i+1))
      = (∑ i ∈ Finset.range 288, stT324 (i+1)) + stT324 289 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 288
    simpa using h
  have hprev := st324_p288
  have hstep := st324_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p290 : ((6446480348023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT324 (i+1))
      = (∑ i ∈ Finset.range 289, stT324 (i+1)) + stT324 290 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 289
    simpa using h
  have hprev := st324_p289
  have hstep := st324_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p291 : ((3210258238311/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT324 (i+1))
      = (∑ i ∈ Finset.range 290, stT324 (i+1)) + stT324 291 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 290
    simpa using h
  have hprev := st324_p290
  have hstep := st324_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p292 : ((13340523562099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT324 (i+1))
      = (∑ i ∈ Finset.range 291, stT324 (i+1)) + stT324 292 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 291
    simpa using h
  have hprev := st324_p291
  have hstep := st324_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p293 : ((13835495016629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT324 (i+1))
      = (∑ i ∈ Finset.range 292, stT324 (i+1)) + stT324 293 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 292
    simpa using h
  have hprev := st324_p292
  have hstep := st324_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p294 : ((2756265023929/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT324 (i+1))
      = (∑ i ∈ Finset.range 293, stT324 (i+1)) + stT324 294 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 293
    simpa using h
  have hprev := st324_p293
  have hstep := st324_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p295 : ((6620041524973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT324 (i+1))
      = (∑ i ∈ Finset.range 294, stT324 (i+1)) + stT324 295 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 294
    simpa using h
  have hprev := st324_p294
  have hstep := st324_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p296 : ((320064117313/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT324 (i+1))
      = (∑ i ∈ Finset.range 295, stT324 (i+1)) + stT324 296 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 295
    simpa using h
  have hprev := st324_p295
  have hstep := st324_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p297 : ((6470415154767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT324 (i+1))
      = (∑ i ∈ Finset.range 296, stT324 (i+1)) + stT324 297 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 296
    simpa using h
  have hprev := st324_p296
  have hstep := st324_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p298 : ((6751655219631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT324 (i+1))
      = (∑ i ∈ Finset.range 297, stT324 (i+1)) + stT324 298 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 297
    simpa using h
  have hprev := st324_p297
  have hstep := st324_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p299 : ((1735919722337/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT324 (i+1))
      = (∑ i ∈ Finset.range 298, stT324 (i+1)) + stT324 299 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 298
    simpa using h
  have hprev := st324_p298
  have hstep := st324_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p300 : ((6843199608063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT324 (i+1))
      = (∑ i ∈ Finset.range 299, stT324 (i+1)) + stT324 300 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 299
    simpa using h
  have hprev := st324_p299
  have hstep := st324_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p301 : ((13115365770471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT324 (i+1))
      = (∑ i ∈ Finset.range 300, stT324 (i+1)) + stT324 301 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 300
    simpa using h
  have hprev := st324_p300
  have hstep := st324_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p302 : ((12774743335503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT324 (i+1))
      = (∑ i ∈ Finset.range 301, stT324 (i+1)) + stT324 302 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 301
    simpa using h
  have hprev := st324_p301
  have hstep := st324_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p303 : ((13018206782283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT324 (i+1))
      = (∑ i ∈ Finset.range 302, stT324 (i+1)) + stT324 303 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 302
    simpa using h
  have hprev := st324_p302
  have hstep := st324_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p304 : ((3397614546807/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT324 (i+1))
      = (∑ i ∈ Finset.range 303, stT324 (i+1)) + stT324 304 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 303
    simpa using h
  have hprev := st324_p303
  have hstep := st324_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p305 : ((3475123702479/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT324 (i+1))
      = (∑ i ∈ Finset.range 304, stT324 (i+1)) + stT324 305 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 304
    simpa using h
  have hprev := st324_p304
  have hstep := st324_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p306 : ((3408064891569/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT324 (i+1))
      = (∑ i ∈ Finset.range 305, stT324 (i+1)) + stT324 306 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 305
    simpa using h
  have hprev := st324_p305
  have hstep := st324_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p307 : ((13061655839289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT324 (i+1))
      = (∑ i ∈ Finset.range 306, stT324 (i+1)) + stT324 307 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 306
    simpa using h
  have hprev := st324_p306
  have hstep := st324_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p308 : ((6383694243689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT324 (i+1))
      = (∑ i ∈ Finset.range 307, stT324 (i+1)) + stT324 308 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 307
    simpa using h
  have hprev := st324_p307
  have hstep := st324_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p309 : ((6521946305689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT324 (i+1))
      = (∑ i ∈ Finset.range 308, stT324 (i+1)) + stT324 309 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 308
    simpa using h
  have hprev := st324_p308
  have hstep := st324_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p310 : ((6805860922213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT324 (i+1))
      = (∑ i ∈ Finset.range 309, stT324 (i+1)) + stT324 310 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 309
    simpa using h
  have hprev := st324_p309
  have hstep := st324_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p311 : ((13904935610609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT324 (i+1))
      = (∑ i ∈ Finset.range 310, stT324 (i+1)) + stT324 311 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 310
    simpa using h
  have hprev := st324_p310
  have hstep := st324_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p312 : ((3408794434229/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT324 (i+1))
      = (∑ i ∈ Finset.range 311, stT324 (i+1)) + stT324 312 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 311
    simpa using h
  have hprev := st324_p311
  have hstep := st324_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p313 : ((261405668851/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT324 (i+1))
      = (∑ i ∈ Finset.range 312, stT324 (i+1)) + stT324 313 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 312
    simpa using h
  have hprev := st324_p312
  have hstep := st324_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p314 : ((638171933023/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT324 (i+1))
      = (∑ i ∈ Finset.range 313, stT324 (i+1)) + stT324 314 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 313
    simpa using h
  have hprev := st324_p313
  have hstep := st324_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p315 : ((3252806917853/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT324 (i+1))
      = (∑ i ∈ Finset.range 314, stT324 (i+1)) + stT324 315 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 314
    simpa using h
  have hprev := st324_p314
  have hstep := st324_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p316 : ((13571518811783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT324 (i+1))
      = (∑ i ∈ Finset.range 315, stT324 (i+1)) + stT324 316 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 315
    simpa using h
  have hprev := st324_p315
  have hstep := st324_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p317 : ((13904848697873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT324 (i+1))
      = (∑ i ∈ Finset.range 316, stT324 (i+1)) + stT324 317 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 316
    simpa using h
  have hprev := st324_p316
  have hstep := st324_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p318 : ((13694203292791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT324 (i+1))
      = (∑ i ∈ Finset.range 317, stT324 (i+1)) + stT324 318 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 317
    simpa using h
  have hprev := st324_p317
  have hstep := st324_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p319 : ((6571093153811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT324 (i+1))
      = (∑ i ∈ Finset.range 318, stT324 (i+1)) + stT324 319 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 318
    simpa using h
  have hprev := st324_p318
  have hstep := st324_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p320 : ((12771313746193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT324 (i+1))
      = (∑ i ∈ Finset.range 319, stT324 (i+1)) + stT324 320 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 319
    simpa using h
  have hprev := st324_p319
  have hstep := st324_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p321 : ((12928546541563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT324 (i+1))
      = (∑ i ∈ Finset.range 320, stT324 (i+1)) + stT324 321 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 320
    simpa using h
  have hprev := st324_p320
  have hstep := st324_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p322 : ((2692894375543/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT324 (i+1))
      = (∑ i ∈ Finset.range 321, stT324 (i+1)) + stT324 322 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 321
    simpa using h
  have hprev := st324_p321
  have hstep := st324_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p323 : ((13880039132653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT324 (i+1))
      = (∑ i ∈ Finset.range 322, stT324 (i+1)) + stT324 323 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 322
    simpa using h
  have hprev := st324_p322
  have hstep := st324_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p324 : ((2758507479197/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT324 (i+1))
      = (∑ i ∈ Finset.range 323, stT324 (i+1)) + stT324 324 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 323
    simpa using h
  have hprev := st324_p323
  have hstep := st324_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p325 : ((6642354592593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT324 (i+1))
      = (∑ i ∈ Finset.range 324, stT324 (i+1)) + stT324 325 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 324
    simpa using h
  have hprev := st324_p324
  have hstep := st324_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p326 : ((1602714058431/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT324 (i+1))
      = (∑ i ∈ Finset.range 325, stT324 (i+1)) + stT324 326 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 325
    simpa using h
  have hprev := st324_p325
  have hstep := st324_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p327 : ((6411560203997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT324 (i+1))
      = (∑ i ∈ Finset.range 326, stT324 (i+1)) + stT324 327 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 326
    simpa using h
  have hprev := st324_p326
  have hstep := st324_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p328 : ((13285281890721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT324 (i+1))
      = (∑ i ∈ Finset.range 327, stT324 (i+1)) + stT324 328 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 327
    simpa using h
  have hprev := st324_p327
  have hstep := st324_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p329 : ((13791405230963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT324 (i+1))
      = (∑ i ∈ Finset.range 328, stT324 (i+1)) + stT324 329 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 328
    simpa using h
  have hprev := st324_p328
  have hstep := st324_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p330 : ((13889911603989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT324 (i+1))
      = (∑ i ∈ Finset.range 329, stT324 (i+1)) + stT324 330 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 329
    simpa using h
  have hprev := st324_p329
  have hstep := st324_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p331 : ((13495443189189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT324 (i+1))
      = (∑ i ∈ Finset.range 330, stT324 (i+1)) + stT324 331 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 330
    simpa using h
  have hprev := st324_p330
  have hstep := st324_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p332 : ((12958270484961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT324 (i+1))
      = (∑ i ∈ Finset.range 331, stT324 (i+1)) + stT324 332 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 331
    simpa using h
  have hprev := st324_p331
  have hstep := st324_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p333 : ((12750140128367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT324 (i+1))
      = (∑ i ∈ Finset.range 332, stT324 (i+1)) + stT324 333 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 332
    simpa using h
  have hprev := st324_p332
  have hstep := st324_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p334 : ((6525441688221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT324 (i+1))
      = (∑ i ∈ Finset.range 333, stT324 (i+1)) + stT324 334 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 333
    simpa using h
  have hprev := st324_p333
  have hstep := st324_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p335 : ((849817239373/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT324 (i+1))
      = (∑ i ∈ Finset.range 334, stT324 (i+1)) + stT324 335 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 334
    simpa using h
  have hprev := st324_p334
  have hstep := st324_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p336 : ((217442337973/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT324 (i+1))
      = (∑ i ∈ Finset.range 335, stT324 (i+1)) + stT324 336 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 335
    simpa using h
  have hprev := st324_p335
  have hstep := st324_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p337 : ((858487345307/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT324 (i+1))
      = (∑ i ∈ Finset.range 336, stT324 (i+1)) + stT324 337 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 336
    simpa using h
  have hprev := st324_p336
  have hstep := st324_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p338 : ((2642396277509/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT324 (i+1))
      = (∑ i ∈ Finset.range 337, stT324 (i+1)) + stT324 338 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 337
    simpa using h
  have hprev := st324_p337
  have hstep := st324_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p339 : ((12790987588039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT324 (i+1))
      = (∑ i ∈ Finset.range 338, stT324 (i+1)) + stT324 339 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 338
    simpa using h
  have hprev := st324_p338
  have hstep := st324_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p340 : ((2565510892183/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT324 (i+1))
      = (∑ i ∈ Finset.range 339, stT324 (i+1)) + stT324 340 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 339
    simpa using h
  have hprev := st324_p339
  have hstep := st324_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p341 : ((531547491701/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT324 (i+1))
      = (∑ i ∈ Finset.range 340, stT324 (i+1)) + stT324 341 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 340
    simpa using h
  have hprev := st324_p340
  have hstep := st324_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p342 : ((13787300180111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT324 (i+1))
      = (∑ i ∈ Finset.range 341, stT324 (i+1)) + stT324 342 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 341
    simpa using h
  have hprev := st324_p341
  have hstep := st324_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p343 : ((2781830742127/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT324 (i+1))
      = (∑ i ∈ Finset.range 342, stT324 (i+1)) + stT324 343 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 342
    simpa using h
  have hprev := st324_p342
  have hstep := st324_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p344 : ((13555415758531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT324 (i+1))
      = (∑ i ∈ Finset.range 343, stT324 (i+1)) + stT324 344 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 343
    simpa using h
  have hprev := st324_p343
  have hstep := st324_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p345 : ((2603786526369/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT324 (i+1))
      = (∑ i ∈ Finset.range 344, stT324 (i+1)) + stT324 345 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 344
    simpa using h
  have hprev := st324_p344
  have hstep := st324_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p346 : ((12738869440857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT324 (i+1))
      = (∑ i ∈ Finset.range 345, stT324 (i+1)) + stT324 346 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 345
    simpa using h
  have hprev := st324_p345
  have hstep := st324_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p347 : ((2588306120021/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT324 (i+1))
      = (∑ i ∈ Finset.range 346, stT324 (i+1)) + stT324 347 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 346
    simpa using h
  have hprev := st324_p346
  have hstep := st324_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p348 : ((2692141775389/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT324 (i+1))
      = (∑ i ∈ Finset.range 347, stT324 (i+1)) + stT324 348 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 347
    simpa using h
  have hprev := st324_p347
  have hstep := st324_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p349 : ((13877378418893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT324 (i+1))
      = (∑ i ∈ Finset.range 348, stT324 (i+1)) + stT324 349 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 348
    simpa using h
  have hprev := st324_p348
  have hstep := st324_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p350 : ((3464688508501/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT324 (i+1))
      = (∑ i ∈ Finset.range 349, stT324 (i+1)) + stT324 350 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 349
    simpa using h
  have hprev := st324_p349
  have hstep := st324_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p351 : ((6710853662319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT324 (i+1))
      = (∑ i ∈ Finset.range 350, stT324 (i+1)) + stT324 351 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 350
    simpa using h
  have hprev := st324_p350
  have hstep := st324_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p352 : ((6457037576917/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT324 (i+1))
      = (∑ i ∈ Finset.range 351, stT324 (i+1)) + stT324 352 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 351
    simpa using h
  have hprev := st324_p351
  have hstep := st324_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p353 : ((3183938578109/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT324 (i+1))
      = (∑ i ∈ Finset.range 352, stT324 (i+1)) + stT324 353 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 352
    simpa using h
  have hprev := st324_p352
  have hstep := st324_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p354 : ((1628094803361/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT324 (i+1))
      = (∑ i ∈ Finset.range 353, stT324 (i+1)) + stT324 354 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 353
    simpa using h
  have hprev := st324_p353
  have hstep := st324_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p355 : ((1694209185383/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT324 (i+1))
      = (∑ i ∈ Finset.range 354, stT324 (i+1)) + stT324 355 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 354
    simpa using h
  have hprev := st324_p354
  have hstep := st324_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p356 : ((434733332903/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT324 (i+1))
      = (∑ i ∈ Finset.range 355, stT324 (i+1)) + stT324 356 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 355
    simpa using h
  have hprev := st324_p355
  have hstep := st324_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p357 : ((2764624297337/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT324 (i+1))
      = (∑ i ∈ Finset.range 356, stT324 (i+1)) + stT324 357 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 356
    simpa using h
  have hprev := st324_p356
  have hstep := st324_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p358 : ((13358467309863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT324 (i+1))
      = (∑ i ∈ Finset.range 357, stT324 (i+1)) + stT324 358 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 357
    simpa using h
  have hprev := st324_p357
  have hstep := st324_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p359 : ((12873719852163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT324 (i+1))
      = (∑ i ∈ Finset.range 358, stT324 (i+1)) + stT324 359 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 358
    simpa using h
  have hprev := st324_p358
  have hstep := st324_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p360 : ((6368410487527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT324 (i+1))
      = (∑ i ∈ Finset.range 359, stT324 (i+1)) + stT324 360 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 359
    simpa using h
  have hprev := st324_p359
  have hstep := st324_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p361 : ((6524713410967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT324 (i+1))
      = (∑ i ∈ Finset.range 360, stT324 (i+1)) + stT324 361 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 360
    simpa using h
  have hprev := st324_p360
  have hstep := st324_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p362 : ((1357457437919/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT324 (i+1))
      = (∑ i ∈ Finset.range 361, stT324 (i+1)) + stT324 362 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 361
    simpa using h
  have hprev := st324_p361
  have hstep := st324_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p363 : ((6959402364007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT324 (i+1))
      = (∑ i ∈ Finset.range 362, stT324 (i+1)) + stT324 363 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 362
    simpa using h
  have hprev := st324_p362
  have hstep := st324_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p364 : ((6913518885787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT324 (i+1))
      = (∑ i ∈ Finset.range 363, stT324 (i+1)) + stT324 364 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 363
    simpa using h
  have hprev := st324_p363
  have hstep := st324_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p365 : ((6684577939003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT324 (i+1))
      = (∑ i ∈ Finset.range 364, stT324 (i+1)) + stT324 365 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 364
    simpa using h
  have hprev := st324_p364
  have hstep := st324_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p366 : ((2576753764663/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT324 (i+1))
      = (∑ i ∈ Finset.range 365, stT324 (i+1)) + stT324 366 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 365
    simpa using h
  have hprev := st324_p365
  have hstep := st324_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p367 : ((12726310295903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT324 (i+1))
      = (∑ i ∈ Finset.range 366, stT324 (i+1)) + stT324 367 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 366
    simpa using h
  have hprev := st324_p366
  have hstep := st324_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p368 : ((13009892486333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT324 (i+1))
      = (∑ i ∈ Finset.range 367, stT324 (i+1)) + stT324 368 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 367
    simpa using h
  have hprev := st324_p367
  have hstep := st324_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p369 : ((13526906561341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT324 (i+1))
      = (∑ i ∈ Finset.range 368, stT324 (i+1)) + stT324 369 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 368
    simpa using h
  have hprev := st324_p368
  have hstep := st324_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p370 : ((1737931308027/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT324 (i+1))
      = (∑ i ∈ Finset.range 369, stT324 (i+1)) + stT324 370 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 369
    simpa using h
  have hprev := st324_p369
  have hstep := st324_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p371 : ((13870029611941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT324 (i+1))
      = (∑ i ∈ Finset.range 370, stT324 (i+1)) + stT324 371 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 370
    simpa using h
  have hprev := st324_p370
  have hstep := st324_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p372 : ((13452363493001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT324 (i+1))
      = (∑ i ∈ Finset.range 371, stT324 (i+1)) + stT324 372 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 371
    simpa using h
  have hprev := st324_p371
  have hstep := st324_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p373 : ((12948819399377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT324 (i+1))
      = (∑ i ∈ Finset.range 372, stT324 (i+1)) + stT324 373 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 372
    simpa using h
  have hprev := st324_p372
  have hstep := st324_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p374 : ((12715565139281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT324 (i+1))
      = (∑ i ∈ Finset.range 373, stT324 (i+1)) + stT324 374 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 373
    simpa using h
  have hprev := st324_p373
  have hstep := st324_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p375 : ((3228830876797/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT324 (i+1))
      = (∑ i ∈ Finset.range 374, stT324 (i+1)) + stT324 375 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 374
    simpa using h
  have hprev := st324_p374
  have hstep := st324_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p376 : ((6703148738519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT324 (i+1))
      = (∑ i ∈ Finset.range 375, stT324 (i+1)) + stT324 376 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 375
    simpa using h
  have hprev := st324_p375
  have hstep := st324_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p377 : ((108166776223/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT324 (i+1))
      = (∑ i ∈ Finset.range 376, stT324 (i+1)) + stT324 377 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 376
    simpa using h
  have hprev := st324_p376
  have hstep := st324_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p378 : ((435267949621/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT324 (i+1))
      = (∑ i ∈ Finset.range 377, stT324 (i+1)) + stT324 378 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 377
    simpa using h
  have hprev := st324_p377
  have hstep := st324_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p379 : ((3400051294679/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT324 (i+1))
      = (∑ i ∈ Finset.range 378, stT324 (i+1)) + stT324 379 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 378
    simpa using h
  have hprev := st324_p378
  have hstep := st324_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p380 : ((6543653501963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT324 (i+1))
      = (∑ i ∈ Finset.range 379, stT324 (i+1)) + stT324 380 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 379
    simpa using h
  have hprev := st324_p379
  have hstep := st324_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p381 : ((6370349038589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT324 (i+1))
      = (∑ i ∈ Finset.range 380, stT324 (i+1)) + stT324 381 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 380
    simpa using h
  have hprev := st324_p380
  have hstep := st324_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p382 : ((6397482799019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT324 (i+1))
      = (∑ i ∈ Finset.range 381, stT324 (i+1)) + stT324 382 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 381
    simpa using h
  have hprev := st324_p381
  have hstep := st324_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p383 : ((6605779099563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT324 (i+1))
      = (∑ i ∈ Finset.range 382, stT324 (i+1)) + stT324 383 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 382
    simpa using h
  have hprev := st324_p382
  have hstep := st324_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p384 : ((3427168023209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT324 (i+1))
      = (∑ i ∈ Finset.range 383, stT324 (i+1)) + stT324 384 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 383
    simpa using h
  have hprev := st324_p383
  have hstep := st324_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p385 : ((13953259332841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT324 (i+1))
      = (∑ i ∈ Finset.range 384, stT324 (i+1)) + stT324 385 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 384
    simpa using h
  have hprev := st324_p384
  have hstep := st324_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p386 : ((689178585991/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT324 (i+1))
      = (∑ i ∈ Finset.range 385, stT324 (i+1)) + stT324 386 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 385
    simpa using h
  have hprev := st324_p385
  have hstep := st324_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p387 : ((13313891482019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT324 (i+1))
      = (∑ i ∈ Finset.range 386, stT324 (i+1)) + stT324 387 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 386
    simpa using h
  have hprev := st324_p386
  have hstep := st324_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p388 : ((12855263867159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT324 (i+1))
      = (∑ i ∈ Finset.range 387, stT324 (i+1)) + stT324 388 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 387
    simpa using h
  have hprev := st324_p387
  have hstep := st324_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p389 : ((1270857812867/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT324 (i+1))
      = (∑ i ∈ Finset.range 388, stT324 (i+1)) + stT324 389 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 388
    simpa using h
  have hprev := st324_p388
  have hstep := st324_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p390 : ((20749105573/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT324 (i+1))
      = (∑ i ∈ Finset.range 389, stT324 (i+1)) + stT324 390 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 389
    simpa using h
  have hprev := st324_p389
  have hstep := st324_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p391 : ((336587795769/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT324 (i+1))
      = (∑ i ∈ Finset.range 390, stT324 (i+1)) + stT324 391 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 390
    simpa using h
  have hprev := st324_p390
  have hstep := st324_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p392 : ((433533717791/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT324 (i+1))
      = (∑ i ∈ Finset.range 391, stT324 (i+1)) + stT324 392 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 391
    simpa using h
  have hprev := st324_p391
  have hstep := st324_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p393 : ((55734415469/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT324 (i+1))
      = (∑ i ∈ Finset.range 392, stT324 (i+1)) + stT324 393 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 392
    simpa using h
  have hprev := st324_p392
  have hstep := st324_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p394 : ((13607844764141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT324 (i+1))
      = (∑ i ∈ Finset.range 393, stT324 (i+1)) + stT324 394 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 393
    simpa using h
  have hprev := st324_p393
  have hstep := st324_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p395 : ((13105183862351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT324 (i+1))
      = (∑ i ∈ Finset.range 394, stT324 (i+1)) + stT324 395 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 394
    simpa using h
  have hprev := st324_p394
  have hstep := st324_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p396 : ((12745321966147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT324 (i+1))
      = (∑ i ∈ Finset.range 395, stT324 (i+1)) + stT324 396 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 395
    simpa using h
  have hprev := st324_p395
  have hstep := st324_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p397 : ((12754831683127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT324 (i+1))
      = (∑ i ∈ Finset.range 396, stT324 (i+1)) + stT324 397 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 396
    simpa using h
  have hprev := st324_p396
  have hstep := st324_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p398 : ((13126079443179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT324 (i+1))
      = (∑ i ∈ Finset.range 397, stT324 (i+1)) + stT324 398 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 397
    simpa using h
  have hprev := st324_p397
  have hstep := st324_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p399 : ((13625194553911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT324 (i+1))
      = (∑ i ∈ Finset.range 398, stT324 (i+1)) + stT324 399 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 398
    simpa using h
  have hprev := st324_p398
  have hstep := st324_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p400 : ((13940851053911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT324 (i+1))
      = (∑ i ∈ Finset.range 399, stT324 (i+1)) + stT324 400 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 399
    simpa using h
  have hprev := st324_p399
  have hstep := st324_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p401 : ((13878233173127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT324 (i+1))
      = (∑ i ∈ Finset.range 400, stT324 (i+1)) + stT324 401 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 400
    simpa using h
  have hprev := st324_p400
  have hstep := st324_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p402 : ((3369401182023/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT324 (i+1))
      = (∑ i ∈ Finset.range 401, stT324 (i+1)) + stT324 402 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 401
    simpa using h
  have hprev := st324_p401
  have hstep := st324_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p403 : ((3246582264271/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT324 (i+1))
      = (∑ i ∈ Finset.range 402, stT324 (i+1)) + stT324 403 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 402
    simpa using h
  have hprev := st324_p402
  have hstep := st324_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p404 : ((12704919872709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT324 (i+1))
      = (∑ i ∈ Finset.range 403, stT324 (i+1)) + stT324 404 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 403
    simpa using h
  have hprev := st324_p403
  have hstep := st324_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p405 : ((12803552136791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT324 (i+1))
      = (∑ i ∈ Finset.range 404, stT324 (i+1)) + stT324 405 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 404
    simpa using h
  have hprev := st324_p404
  have hstep := st324_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p406 : ((13220832617009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT324 (i+1))
      = (∑ i ∈ Finset.range 405, stT324 (i+1)) + stT324 406 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 405
    simpa using h
  have hprev := st324_p405
  have hstep := st324_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p407 : ((6851974795351/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT324 (i+1))
      = (∑ i ∈ Finset.range 406, stT324 (i+1)) + stT324 407 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 406
    simpa using h
  have hprev := st324_p406
  have hstep := st324_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p408 : ((6981443315873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT324 (i+1))
      = (∑ i ∈ Finset.range 407, stT324 (i+1)) + stT324 408 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 407
    simpa using h
  have hprev := st324_p407
  have hstep := st324_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p409 : ((13844035568437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT324 (i+1))
      = (∑ i ∈ Finset.range 408, stT324 (i+1)) + stT324 409 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 408
    simpa using h
  have hprev := st324_p408
  have hstep := st324_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p410 : ((6709811154761/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT324 (i+1))
      = (∑ i ∈ Finset.range 409, stT324 (i+1)) + stT324 410 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 409
    simpa using h
  have hprev := st324_p409
  have hstep := st324_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p411 : ((6470965327001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT324 (i+1))
      = (∑ i ∈ Finset.range 410, stT324 (i+1)) + stT324 411 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 410
    simpa using h
  have hprev := st324_p410
  have hstep := st324_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p412 : ((12692354940307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT324 (i+1))
      = (∑ i ∈ Finset.range 411, stT324 (i+1)) + stT324 412 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 411
    simpa using h
  have hprev := st324_p411
  have hstep := st324_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p413 : ((3204028308819/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT324 (i+1))
      = (∑ i ∈ Finset.range 412, stT324 (i+1)) + stT324 413 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 412
    simpa using h
  have hprev := st324_p412
  have hstep := st324_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p414 : ((3309847360449/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT324 (i+1))
      = (∑ i ∈ Finset.range 413, stT324 (i+1)) + stT324 414 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 413
    simpa using h
  have hprev := st324_p413
  have hstep := st324_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p415 : ((3428776785089/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT324 (i+1))
      = (∑ i ∈ Finset.range 414, stT324 (i+1)) + stT324 415 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 414
    simpa using h
  have hprev := st324_p414
  have hstep := st324_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p416 : ((1746009278377/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT324 (i+1))
      = (∑ i ∈ Finset.range 415, stT324 (i+1)) + stT324 416 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 415
    simpa using h
  have hprev := st324_p415
  have hstep := st324_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p417 : ((6926837354593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT324 (i+1))
      = (∑ i ∈ Finset.range 416, stT324 (i+1)) + stT324 417 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 416
    simpa using h
  have hprev := st324_p416
  have hstep := st324_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p418 : ((1343897721947/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT324 (i+1))
      = (∑ i ∈ Finset.range 417, stT324 (i+1)) + stT324 418 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 417
    simpa using h
  have hprev := st324_p417
  have hstep := st324_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p419 : ((6480829002967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT324 (i+1))
      = (∑ i ∈ Finset.range 418, stT324 (i+1)) + stT324 419 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 418
    simpa using h
  have hprev := st324_p418
  have hstep := st324_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p420 : ((6346424851821/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT324 (i+1))
      = (∑ i ∈ Finset.range 419, stT324 (i+1)) + stT324 420 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 419
    simpa using h
  have hprev := st324_p419
  have hstep := st324_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p421 : ((3195875252753/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT324 (i+1))
      = (∑ i ∈ Finset.range 420, stT324 (i+1)) + stT324 421 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 420
    simpa using h
  have hprev := st324_p420
  have hstep := st324_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p422 : ((3295268808407/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT324 (i+1))
      = (∑ i ∈ Finset.range 421, stT324 (i+1)) + stT324 422 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 421
    simpa using h
  have hprev := st324_p421
  have hstep := st324_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p423 : ((3415410472481/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT324 (i+1))
      = (∑ i ∈ Finset.range 422, stT324 (i+1)) + stT324 423 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 422
    simpa using h
  have hprev := st324_p422
  have hstep := st324_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p424 : ((3489241654457/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT324 (i+1))
      = (∑ i ∈ Finset.range 423, stT324 (i+1)) + stT324 424 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 423
    simpa using h
  have hprev := st324_p423
  have hstep := st324_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p425 : ((3475984394161/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT324 (i+1))
      = (∑ i ∈ Finset.range 424, stT324 (i+1)) + stT324 425 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 424
    simpa using h
  have hprev := st324_p424
  have hstep := st324_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p426 : ((676664386631/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT324 (i+1))
      = (∑ i ∈ Finset.range 425, stT324 (i+1)) + stT324 426 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 425
    simpa using h
  have hprev := st324_p425
  have hstep := st324_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p427 : ((6525085064639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT324 (i+1))
      = (∑ i ∈ Finset.range 426, stT324 (i+1)) + stT324 427 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 426
    simpa using h
  have hprev := st324_p426
  have hstep := st324_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p428 : ((794970702013/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT324 (i+1))
      = (∑ i ∈ Finset.range 427, stT324 (i+1)) + stT324 428 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 427
    simpa using h
  have hprev := st324_p427
  have hstep := st324_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p429 : ((3180234651467/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT324 (i+1))
      = (∑ i ∈ Finset.range 428, stT324 (i+1)) + stT324 429 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 428
    simpa using h
  have hprev := st324_p428
  have hstep := st324_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p430 : ((6526100863617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT324 (i+1))
      = (∑ i ∈ Finset.range 429, stT324 (i+1)) + stT324 430 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 429
    simpa using h
  have hprev := st324_p429
  have hstep := st324_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p431 : ((13532945927067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT324 (i+1))
      = (∑ i ∈ Finset.range 430, stT324 (i+1)) + stT324 431 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 430
    simpa using h
  have hprev := st324_p430
  have hstep := st324_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p432 : ((3475987398423/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT324 (i+1))
      = (∑ i ∈ Finset.range 431, stT324 (i+1)) + stT324 432 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 431
    simpa using h
  have hprev := st324_p431
  have hstep := st324_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p433 : ((13966961320403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT324 (i+1))
      = (∑ i ∈ Finset.range 432, stT324 (i+1)) + stT324 433 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 432
    simpa using h
  have hprev := st324_p432
  have hstep := st324_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p434 : ((13689648396947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT324 (i+1))
      = (∑ i ∈ Finset.range 433, stT324 (i+1)) + stT324 434 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 433
    simpa using h
  have hprev := st324_p433
  have hstep := st324_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p435 : ((13220600752347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT324 (i+1))
      = (∑ i ∈ Finset.range 434, stT324 (i+1)) + stT324 435 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 434
    simpa using h
  have hprev := st324_p434
  have hstep := st324_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p436 : ((12808476098787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT324 (i+1))
      = (∑ i ∈ Finset.range 435, stT324 (i+1)) + stT324 436 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 435
    simpa using h
  have hprev := st324_p435
  have hstep := st324_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p437 : ((12669860272737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT324 (i+1))
      = (∑ i ∈ Finset.range 436, stT324 (i+1)) + stT324 437 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 436
    simpa using h
  have hprev := st324_p436
  have hstep := st324_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p438 : ((12876233689481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT324 (i+1))
      = (∑ i ∈ Finset.range 437, stT324 (i+1)) + stT324 438 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 437
    simpa using h
  have hprev := st324_p437
  have hstep := st324_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p439 : ((6659243391553/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT324 (i+1))
      = (∑ i ∈ Finset.range 438, stT324 (i+1)) + stT324 439 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 438
    simpa using h
  have hprev := st324_p438
  have hstep := st324_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p440 : ((13765939348741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT324 (i+1))
      = (∑ i ∈ Finset.range 439, stT324 (i+1)) + stT324 440 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 439
    simpa using h
  have hprev := st324_p439
  have hstep := st324_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p441 : ((13987171984651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT324 (i+1))
      = (∑ i ∈ Finset.range 440, stT324 (i+1)) + stT324 441 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 440
    simpa using h
  have hprev := st324_p440
  have hstep := st324_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p442 : ((13869180798227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT324 (i+1))
      = (∑ i ∈ Finset.range 441, stT324 (i+1)) + stT324 442 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 441
    simpa using h
  have hprev := st324_p441
  have hstep := st324_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p443 : ((1684227028319/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT324 (i+1))
      = (∑ i ∈ Finset.range 442, stT324 (i+1)) + stT324 443 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 442
    simpa using h
  have hprev := st324_p442
  have hstep := st324_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p444 : ((1300400294887/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT324 (i+1))
      = (∑ i ∈ Finset.range 443, stT324 (i+1)) + stT324 444 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 443
    simpa using h
  have hprev := st324_p443
  have hstep := st324_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p445 : ((396837568097/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT324 (i+1))
      = (∑ i ∈ Finset.range 444, stT324 (i+1)) + stT324 445 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 444
    simpa using h
  have hprev := st324_p444
  have hstep := st324_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p446 : ((12711979572381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT324 (i+1))
      = (∑ i ∈ Finset.range 445, stT324 (i+1)) + stT324 446 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 445
    simpa using h
  have hprev := st324_p445
  have hstep := st324_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p447 : ((1629445829373/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT324 (i+1))
      = (∑ i ∈ Finset.range 446, stT324 (i+1)) + stT324 447 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 446
    simpa using h
  have hprev := st324_p446
  have hstep := st324_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p448 : ((13505924407239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT324 (i+1))
      = (∑ i ∈ Finset.range 447, stT324 (i+1)) + stT324 448 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 447
    simpa using h
  have hprev := st324_p447
  have hstep := st324_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p449 : ((1388743133891/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT324 (i+1))
      = (∑ i ∈ Finset.range 448, stT324 (i+1)) + stT324 449 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 448
    simpa using h
  have hprev := st324_p448
  have hstep := st324_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p450 : ((6995311780063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT324 (i+1))
      = (∑ i ∈ Finset.range 449, stT324 (i+1)) + stT324 450 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 449
    simpa using h
  have hprev := st324_p449
  have hstep := st324_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p451 : ((1720684563941/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT324 (i+1))
      = (∑ i ∈ Finset.range 450, stT324 (i+1)) + stT324 451 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 450
    simpa using h
  have hprev := st324_p450
  have hstep := st324_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p452 : ((532974445897/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT324 (i+1))
      = (∑ i ∈ Finset.range 451, stT324 (i+1)) + stT324 452 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 451
    simpa using h
  have hprev := st324_p451
  have hstep := st324_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p453 : ((12884800460193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT324 (i+1))
      = (∑ i ∈ Finset.range 452, stT324 (i+1)) + stT324 453 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 452
    simpa using h
  have hprev := st324_p452
  have hstep := st324_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p454 : ((12661761738377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT324 (i+1))
      = (∑ i ∈ Finset.range 453, stT324 (i+1)) + stT324 454 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 453
    simpa using h
  have hprev := st324_p453
  have hstep := st324_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p455 : ((510520286933/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT324 (i+1))
      = (∑ i ∈ Finset.range 454, stT324 (i+1)) + stT324 455 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 454
    simpa using h
  have hprev := st324_p454
  have hstep := st324_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p456 : ((13138097826317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT324 (i+1))
      = (∑ i ∈ Finset.range 455, stT324 (i+1)) + stT324 456 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 455
    simpa using h
  have hprev := st324_p455
  have hstep := st324_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p457 : ((13604749540957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT324 (i+1))
      = (∑ i ∈ Finset.range 456, stT324 (i+1)) + stT324 457 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 456
    simpa using h
  have hprev := st324_p456
  have hstep := st324_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p458 : ((13938131954387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT324 (i+1))
      = (∑ i ∈ Finset.range 457, stT324 (i+1)) + stT324 458 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 457
    simpa using h
  have hprev := st324_p457
  have hstep := st324_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p459 : ((13979062605547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT324 (i+1))
      = (∑ i ∈ Finset.range 458, stT324 (i+1)) + stT324 459 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 458
    simpa using h
  have hprev := st324_p458
  have hstep := st324_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p460 : ((6854588126387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT324 (i+1))
      = (∑ i ∈ Finset.range 459, stT324 (i+1)) + stT324 460 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 459
    simpa using h
  have hprev := st324_p459
  have hstep := st324_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p461 : ((13257863218051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT324 (i+1))
      = (∑ i ∈ Finset.range 460, stT324 (i+1)) + stT324 461 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 460
    simpa using h
  have hprev := st324_p460
  have hstep := st324_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p462 : ((2567860354037/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT324 (i+1))
      = (∑ i ∈ Finset.range 461, stT324 (i+1)) + stT324 462 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 461
    simpa using h
  have hprev := st324_p461
  have hstep := st324_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p463 : ((506020436189/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT324 (i+1))
      = (∑ i ∈ Finset.range 462, stT324 (i+1)) + stT324 463 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 462
    simpa using h
  have hprev := st324_p462
  have hstep := st324_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p464 : ((2555824680049/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT324 (i+1))
      = (∑ i ∈ Finset.range 463, stT324 (i+1)) + stT324 464 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 463
    simpa using h
  have hprev := st324_p463
  have hstep := st324_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p465 : ((2632756959297/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT324 (i+1))
      = (∑ i ∈ Finset.range 464, stT324 (i+1)) + stT324 465 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 464
    simpa using h
  have hprev := st324_p464
  have hstep := st324_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p466 : ((6812248481933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT324 (i+1))
      = (∑ i ∈ Finset.range 465, stT324 (i+1)) + stT324 466 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 465
    simpa using h
  have hprev := st324_p465
  have hstep := st324_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p467 : ((1394747654257/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT324 (i+1))
      = (∑ i ∈ Finset.range 466, stT324 (i+1)) + stT324 467 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 466
    simpa using h
  have hprev := st324_p466
  have hstep := st324_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p468 : ((699210646841/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT324 (i+1))
      = (∑ i ∈ Finset.range 467, stT324 (i+1)) + stT324 468 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 467
    simpa using h
  have hprev := st324_p467
  have hstep := st324_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p469 : ((6859457016871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT324 (i+1))
      = (∑ i ∈ Finset.range 468, stT324 (i+1)) + stT324 469 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 468
    simpa using h
  have hprev := st324_p468
  have hstep := st324_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p470 : ((3318541146351/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT324 (i+1))
      = (∑ i ∈ Finset.range 469, stT324 (i+1)) + stT324 470 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 469
    simpa using h
  have hprev := st324_p469
  have hstep := st324_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p471 : ((128533590603/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT324 (i+1))
      = (∑ i ∈ Finset.range 470, stT324 (i+1)) + stT324 471 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 470
    simpa using h
  have hprev := st324_p470
  have hstep := st324_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p472 : ((632370504951/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT324 (i+1))
      = (∑ i ∈ Finset.range 471, stT324 (i+1)) + stT324 472 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 471
    simpa using h
  have hprev := st324_p471
  have hstep := st324_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p473 : ((637428603821/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT324 (i+1))
      = (∑ i ∈ Finset.range 472, stT324 (i+1)) + stT324 473 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 472
    simpa using h
  have hprev := st324_p472
  have hstep := st324_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p474 : ((524403533947/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT324 (i+1))
      = (∑ i ∈ Finset.range 473, stT324 (i+1)) + stT324 474 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 473
    simpa using h
  have hprev := st324_p473
  have hstep := st324_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p475 : ((6784398420399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT324 (i+1))
      = (∑ i ∈ Finset.range 474, stT324 (i+1)) + stT324 475 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 474
    simpa using h
  have hprev := st324_p474
  have hstep := st324_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p476 : ((13919426950563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT324 (i+1))
      = (∑ i ∈ Finset.range 475, stT324 (i+1)) + stT324 476 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 475
    simpa using h
  have hprev := st324_p475
  have hstep := st324_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p477 : ((14006404929447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT324 (i+1))
      = (∑ i ∈ Finset.range 476, stT324 (i+1)) + stT324 477 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 476
    simpa using h
  have hprev := st324_p476
  have hstep := st324_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p478 : ((13792179004707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT324 (i+1))
      = (∑ i ∈ Finset.range 477, stT324 (i+1)) + stT324 478 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 477
    simpa using h
  have hprev := st324_p477
  have hstep := st324_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p479 : ((13372432226787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT324 (i+1))
      = (∑ i ∈ Finset.range 478, stT324 (i+1)) + stT324 479 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 478
    simpa using h
  have hprev := st324_p478
  have hstep := st324_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p480 : ((12932409208911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT324 (i+1))
      = (∑ i ∈ Finset.range 479, stT324 (i+1)) + stT324 480 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 479
    simpa using h
  have hprev := st324_p479
  have hstep := st324_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p481 : ((3166196066961/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT324 (i+1))
      = (∑ i ∈ Finset.range 480, stT324 (i+1)) + stT324 481 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 480
    simpa using h
  have hprev := st324_p480
  have hstep := st324_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p482 : ((3171393173631/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT324 (i+1))
      = (∑ i ∈ Finset.range 481, stT324 (i+1)) + stT324 482 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 481
    simpa using h
  have hprev := st324_p481
  have hstep := st324_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p483 : ((405769187897/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT324 (i+1))
      = (∑ i ∈ Finset.range 482, stT324 (i+1)) + stT324 483 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 482
    simpa using h
  have hprev := st324_p482
  have hstep := st324_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p484 : ((13431488565829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT324 (i+1))
      = (∑ i ∈ Finset.range 483, stT324 (i+1)) + stT324 484 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 483
    simpa using h
  have hprev := st324_p483
  have hstep := st324_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p485 : ((13833092905497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT324 (i+1))
      = (∑ i ∈ Finset.range 484, stT324 (i+1)) + stT324 485 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 484
    simpa using h
  have hprev := st324_p484
  have hstep := st324_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p486 : ((14017240015137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT324 (i+1))
      = (∑ i ∈ Finset.range 485, stT324 (i+1)) + stT324 486 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 485
    simpa using h
  have hprev := st324_p485
  have hstep := st324_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p487 : ((13906032133521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT324 (i+1))
      = (∑ i ∈ Finset.range 486, stT324 (i+1)) + stT324 487 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 486
    simpa using h
  have hprev := st324_p486
  have hstep := st324_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p488 : ((2709582287823/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT324 (i+1))
      = (∑ i ∈ Finset.range 487, stT324 (i+1)) + stT324 488 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 487
    simpa using h
  have hprev := st324_p487
  have hstep := st324_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p489 : ((13095655644107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT324 (i+1))
      = (∑ i ∈ Finset.range 488, stT324 (i+1)) + stT324 489 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 488
    simpa using h
  have hprev := st324_p488
  have hstep := st324_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p490 : ((12740619013229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT324 (i+1))
      = (∑ i ∈ Finset.range 489, stT324 (i+1)) + stT324 490 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 489
    simpa using h
  have hprev := st324_p489
  have hstep := st324_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p491 : ((12631797588421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT324 (i+1))
      = (∑ i ∈ Finset.range 490, stT324 (i+1)) + stT324 491 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 490
    simpa using h
  have hprev := st324_p490
  have hstep := st324_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p492 : ((12813846611791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT324 (i+1))
      = (∑ i ∈ Finset.range 491, stT324 (i+1)) + stT324 492 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 491
    simpa using h
  have hprev := st324_p491
  have hstep := st324_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p493 : ((13209655033717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT324 (i+1))
      = (∑ i ∈ Finset.range 492, stT324 (i+1)) + stT324 493 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 492
    simpa using h
  have hprev := st324_p492
  have hstep := st324_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p494 : ((6826914146471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT324 (i+1))
      = (∑ i ∈ Finset.range 493, stT324 (i+1)) + stT324 494 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 493
    simpa using h
  have hprev := st324_p493
  have hstep := st324_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p495 : ((349054869499/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT324 (i+1))
      = (∑ i ∈ Finset.range 494, stT324 (i+1)) + stT324 495 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 494
    simpa using h
  have hprev := st324_p494
  have hstep := st324_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p496 : ((175100150831/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT324 (i+1))
      = (∑ i ∈ Finset.range 495, stT324 (i+1)) + stT324 496 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 495
    simpa using h
  have hprev := st324_p495
  have hstep := st324_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p497 : ((43041919189/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT324 (i+1))
      = (∑ i ∈ Finset.range 496, stT324 (i+1)) + stT324 497 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 496
    simpa using h
  have hprev := st324_p496
  have hstep := st324_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p498 : ((6677735434611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT324 (i+1))
      = (∑ i ∈ Finset.range 497, stT324 (i+1)) + stT324 498 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 497
    simpa using h
  have hprev := st324_p497
  have hstep := st324_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p499 : ((3231319272031/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT324 (i+1))
      = (∑ i ∈ Finset.range 498, stT324 (i+1)) + stT324 499 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 498
    simpa using h
  have hprev := st324_p498
  have hstep := st324_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_p500 : ((6328808189313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT324 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT324 (i+1))
      = (∑ i ∈ Finset.range 499, stT324 (i+1)) + stT324 500 := by
    have h := Finset.sum_range_succ (fun i => stT324 (i+1)) 499
    simpa using h
  have hprev := st324_p499
  have hstep := st324_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st324_s500 :
    |Real.sin (((324 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))
      - ((-100149/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -5530769/10000000) (δ := 16397/1000000000) (ψ := -72323/62500) 324 321
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 324`** (evaluated boundary). -/
theorem station_324_sign : 0 < hardyG ((((324:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 324 500 (by norm_num) (by norm_num)
    ((-72323/62500 : ℚ) : ℝ)
  have hchain := st324_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT324 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((324 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-72323/62500 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st324_c500
  have hsinb := abs_le.mp st324_s500
  have hbdy_lo : ((232419244942599/4199050000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((324 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-72323/62500 : ℚ) : ℝ))) / 2
          - ((((324:ℕ)):ℝ))
            * Real.sin (((324 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-72323/62500 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((324:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((324:ℝ) * Real.log (500:ℝ) - ((-72323/62500 : ℚ) : ℝ))) / 2
        - ((324:ℝ)) * Real.sin ((324:ℝ) * Real.log (500:ℝ) - ((-72323/62500 : ℚ) : ℝ))
        ≥ ((519705923/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((324:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((519705923/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((519705923/2000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((519705923/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((324:ℕ)):ℝ))+1) * (((((324:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((488661122699/600000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((6328808189313/5000000000000 : ℚ) : ℝ) + ((232419244942599/4199050000000000 : ℚ) : ℝ)
      - ((488661122699/600000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-72323/62500 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((324:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-72323/62500 : ℚ) : ℝ)
        * (riemannZeta (line ((((324:ℕ)):ℝ)))).re
      - Real.sin ((-72323/62500 : ℚ) : ℝ)
        * (riemannZeta (line ((((324:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((324:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((324:ℕ)):ℝ))
      = (((((324:ℕ)):ℝ)) * (Real.log ((((324:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((324:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_324
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
  have hθwin : |(((-72323/62500 : ℚ) : ℝ) + ((76:ℤ)) * (2*Real.pi)) - theta ((((324:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((324:ℕ)):ℝ)))
    (φ := ((-72323/62500 : ℚ) : ℝ) + ((76:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-72323/62500 : ℚ)) : ℝ) 76).1,
    (cos_sin_shift (((-72323/62500 : ℚ)) : ℝ) 76).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_324_sign
end AxiomAudit
