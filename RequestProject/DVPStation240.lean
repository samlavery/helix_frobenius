import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 240` (rung-262.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT240 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((240 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-109777/200000 : ℚ) : ℝ))

theorem st240_c1 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((853107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 343053/2500000) (δ := 201/1000000000) (ψ := -109777/200000) 240 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t1 : ((853057/1000000 : ℚ) : ℝ) ≤ stT240 1 := by
  have hc : ((853057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((853057/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((853057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c2 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-921143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3427253/5000000) (δ := 3027/250000000) (ψ := -109777/200000) 240 27
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t2 : ((-1628454586031/2500000000000 : ℚ) : ℝ) ≤ stT240 2 := by
  have hc : ((-921193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1628454586031/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-921193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c3 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((948591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 161021/2000000) (δ := 121/10000000) (ψ := -109777/200000) 240 42
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t3 : ((2738201680291/5000000000000 : ℚ) : ℝ) ≤ stT240 3 := by
  have hc : ((948541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2738201680291/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((948541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c4 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((968737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 626769/10000000) (δ := 12121/1000000000) (ψ := -109777/200000) 240 53
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t4 : ((968687/2000000 : ℚ) : ℝ) ≤ stT240 4 := by
  have hc : ((968687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((968687/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((968687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c5 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-921801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -342937/500000) (δ := 12047/1000000000) (ψ := -109777/200000) 240 62
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t5 : ((-515330380467/1250000000000 : ℚ) : ℝ) ≤ stT240 5 := by
  have hc : ((-921851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-515330380467/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-921851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c6 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-24627/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7421583/10000000) (δ := 6003/500000000) (ψ := -109777/200000) 240 69
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t6 : ((-402177647779/1000000000000 : ℚ) : ℝ) ≤ stT240 6 := by
  have hc : ((-98513/100000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-402177647779/1000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-98513/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c7 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-172563/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6529021/10000000) (δ := 12133/1000000000) (ψ := -109777/200000) 240 74
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t7 : ((-130452935317/400000000000 : ℚ) : ℝ) ≤ stT240 7 := by
  have hc : ((-172573/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130452935317/400000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-172573/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c8 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-994841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7599919/10000000) (δ := 12027/1000000000) (ψ := -109777/200000) 240 80
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t8 : ((-1758735478397/5000000000000 : ℚ) : ℝ) ≤ stT240 8 := by
  have hc : ((-994891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1758735478397/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-994891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c9 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((995471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 59507/2500000) (δ := 2401/200000000) (ψ := -109777/200000) 240 84
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t9 : ((3318069668193/10000000000000 : ℚ) : ℝ) ≤ stT240 9 := by
  have hc : ((995421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3318069668193/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((995421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c10 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((484581/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24899/400000) (δ := 12033/1000000000) (ψ := -109777/200000) 240 88
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t10 : ((383075073503/1250000000000 : ℚ) : ℝ) ≤ stT240 10 := by
  have hc : ((121139/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((383075073503/1250000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((121139/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c11 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-106147/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2511629/5000000) (δ := 6031/500000000) (ψ := -109777/200000) 240 92
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t11 : ((-320082994683/2500000000000 : ℚ) : ℝ) ≤ stT240 11 := by
  have hc : ((-212319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-320082994683/2500000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-212319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c12 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((199943/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14923/2500000) (δ := 12019/1000000000) (ψ := -109777/200000) 240 95
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t12 : ((577156787683/2000000000000 : ℚ) : ℝ) ≤ stT240 12 := by
  have hc : ((199933/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((577156787683/2000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((199933/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c13 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((11587/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 480711/5000000) (δ := 6049/500000000) (ψ := -109777/200000) 240 98
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t13 : ((514156977/2000000000 : ℚ) : ℝ) ≤ stT240 13 := by
  have hc : ((92691/100000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((514156977/2000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((92691/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c14 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((778159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -424417/2500000) (δ := 761/62500000) (ψ := -109777/200000) 240 101
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t14 : ((519895862677/2500000000000 : ℚ) : ℝ) ≤ stT240 14 := by
  have hc : ((778109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((519895862677/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((778109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c15 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-98537/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7425817/10000000) (δ := 3037/250000000) (ψ := -109777/200000) 240 104
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t15 : ((-127217180019/500000000000 : ℚ) : ℝ) ≤ stT240 15 := by
  have hc : ((-49271/50000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127217180019/500000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-49271/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c16 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((499437/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29661/2500000) (δ := 301/25000000) (ψ := -109777/200000) 240 106
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t16 : ((124853/500000 : ℚ) : ℝ) ≤ stT240 16 := by
  have hc : ((124853/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124853/500000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((124853/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c17 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-357211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 484019/1000000) (δ := 12177/1000000000) (ψ := -109777/200000) 240 108
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t17 : ((-866485467177/10000000000000 : ℚ) : ℝ) ≤ stT240 17 := by
  have hc : ((-357261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-866485467177/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-357261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c18 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-998549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7719303/10000000) (δ := 3003/250000000) (ψ := -109777/200000) 240 110
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t18 : ((-2353720810777/10000000000000 : ℚ) : ℝ) ≤ stT240 18 := by
  have hc : ((-998599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2353720810777/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-998599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c19 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-468669/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6964267/10000000) (δ := 1209/100000000) (ψ := -109777/200000) 240 113
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t19 : ((-268814522413/1250000000000 : ℚ) : ℝ) ≤ stT240 19 := by
  have hc : ((-234347/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-268814522413/1250000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-234347/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c20 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-995013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7604213/10000000) (δ := 12127/1000000000) (ψ := -109777/200000) 240 115
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t20 : ((-556257133071/2500000000000 : ℚ) : ℝ) ≤ stT240 20 := by
  have hc : ((-995063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-556257133071/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-995063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c21 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-363513/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5961943/10000000) (δ := 12169/1000000000) (ψ := -109777/200000) 240 116
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t21 : ((-396652494651/2500000000000 : ℚ) : ℝ) ≤ stT240 21 := by
  have hc : ((-181769/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-396652494651/2500000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-181769/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c22 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((138589/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2458017/10000000) (δ := 12049/1000000000) (ψ := -109777/200000) 240 118
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t22 : ((590892136071/5000000000000 : ℚ) : ℝ) ≤ stT240 22 := by
  have hc : ((277153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((590892136071/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((277153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c23 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((610003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -228683/1000000) (δ := 607/50000000) (ψ := -109777/200000) 240 120
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t23 : ((158979979779/1250000000000 : ℚ) : ℝ) ≤ stT240 23 := by
  have hc : ((609953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158979979779/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((609953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c24 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-248043/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7540967/10000000) (δ := 12033/1000000000) (ψ := -109777/200000) 240 121
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t24 : ((-506341304931/2500000000000 : ℚ) : ℝ) ≤ stT240 24 := by
  have hc : ((-496111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-506341304931/2500000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-496111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c25 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((484789/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 618241/10000000) (δ := 2437/200000000) (ψ := -109777/200000) 240 123
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t25 : ((121191/625000 : ℚ) : ℝ) ≤ stT240 25 := by
  have hc : ((121191/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121191/625000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((121191/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c26 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-972401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3632633/5000000) (δ := 3001/250000000) (ψ := -109777/200000) 240 125
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t26 : ((-953566974031/5000000000000 : ℚ) : ℝ) ≤ stT240 26 := by
  have hc : ((-972451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-953566974031/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-972451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c27 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((991351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -329049/10000000) (δ := 6053/500000000) (ψ := -109777/200000) 240 126
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t27 : ((3815517549/20000000000 : ℚ) : ℝ) ≤ stT240 27 := by
  have hc : ((991301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3815517549/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((991301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c28 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-8453/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5783607/10000000) (δ := 1219/100000000) (ψ := -109777/200000) 240 127
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t28 : ((-127806839667/1000000000000 : ℚ) : ℝ) ≤ stT240 28 := by
  have hc : ((-67629/100000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127806839667/1000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-67629/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c29 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-64323/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4577539/10000000) (δ := 3007/250000000) (ψ := -109777/200000) 240 129
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t29 : ((-119468064067/2500000000000 : ℚ) : ℝ) ≤ stT240 29 := by
  have hc : ((-128671/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119468064067/2500000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-128671/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c30 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((499877/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27699/5000000) (δ := 2427/200000000) (ψ := -109777/200000) 240 130
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t30 : ((228150072583/1250000000000 : ℚ) : ℝ) ≤ stT240 30 := by
  have hc : ((124963/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228150072583/1250000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((124963/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c31 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-2359/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2010687/5000000) (δ := 12161/1000000000) (ψ := -109777/200000) 240 131
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t31 : ((-16970016219/2500000000000 : ℚ) : ℝ) ≤ stT240 31 := by
  have hc : ((-18897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16970016219/2500000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-18897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c32 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-245187/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7362631/10000000) (δ := 6027/500000000) (ψ := -109777/200000) 240 132
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t32 : ((-866911169033/5000000000000 : ℚ) : ℝ) ≤ stT240 32 := by
  have hc : ((-490399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-866911169033/5000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-490399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c33 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-24693/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1118067/2000000) (δ := 3041/250000000) (ψ := -109777/200000) 240 134
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t33 : ((-8597697603/80000000000 : ℚ) : ℝ) ≤ stT240 33 := by
  have hc : ((-4939/8000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8597697603/80000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-4939/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c34 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((53629/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3386499/10000000) (δ := 3033/250000000) (ψ := -109777/200000) 240 135
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t34 : ((36780597301/1000000000000 : ℚ) : ℝ) ≤ stT240 34 := by
  have hc : ((107233/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36780597301/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((107233/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c35 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((777079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -850981/5000000) (δ := 481/40000000) (ψ := -109777/200000) 240 136
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t35 : ((328354583733/2500000000000 : ℚ) : ℝ) ≤ stT240 35 := by
  have hc : ((777029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((328354583733/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((777029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c36 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((39179/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -101477/2000000) (δ := 2417/200000000) (ψ := -109777/200000) 240 137
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t36 : ((32647486941/200000000000 : ℚ) : ℝ) ≤ stT240 36 := by
  have hc : ((39177/40000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32647486941/200000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((39177/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c37 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((995987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56013/2500000) (δ := 381/31250000) (ψ := -109777/200000) 240 138
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t37 : ((1637309472693/10000000000000 : ℚ) : ℝ) ≤ stT240 37 := by
  have hc : ((995937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1637309472693/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((995937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c38 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((244673/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 32313/625000) (δ := 1513/125000000) (ψ := -109777/200000) 240 139
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t38 : ((396891688347/2500000000000 : ℚ) : ℝ) ≤ stT240 38 := by
  have hc : ((489321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((396891688347/2500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((489321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c39 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((197517/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 78869/2000000) (δ := 12007/1000000000) (ψ := -109777/200000) 240 140
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t39 : ((316264206467/2000000000000 : ℚ) : ℝ) ≤ stT240 39 := by
  have hc : ((197507/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((316264206467/2000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((197507/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c40 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((998791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -61469/5000000) (δ := 6057/500000000) (ψ := -109777/200000) 240 141
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t40 : ((789573673629/5000000000000 : ℚ) : ℝ) ≤ stT240 40 := by
  have hc : ((998741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((789573673629/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((998741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c41 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((459327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -507671/5000000) (δ := 6091/500000000) (ψ := -109777/200000) 240 142
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t41 : ((358654463787/2500000000000 : ℚ) : ℝ) ≤ stT240 41 := by
  have hc : ((229651/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((358654463787/2500000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((229651/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c42 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((616979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -452949/2000000) (δ := 483/40000000) (ψ := -109777/200000) 240 143
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t42 : ((951941805657/10000000000000 : ℚ) : ℝ) ≤ stT240 42 := by
  have hc : ((616929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((951941805657/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((616929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c43 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((29029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -481801/1250000) (δ := 2407/200000000) (ψ := -109777/200000) 240 144
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t43 : ((8838508063/2000000000000 : ℚ) : ℝ) ≤ stT240 43 := by
  have hc : ((28979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8838508063/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((28979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c44 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-671827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5768671/10000000) (δ := 12143/1000000000) (ψ := -109777/200000) 240 145
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t44 : ((-1012892874489/10000000000000 : ℚ) : ℝ) ≤ stT240 44 := by
  have hc : ((-671877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1012892874489/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-671877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c45 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-199691/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7715009/10000000) (δ := 12143/1000000000) (ψ := -109777/200000) 240 145
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t45 : ((-37212084639/250000000000 : ℚ) : ℝ) ≤ stT240 45 := by
  have hc : ((-199701/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37212084639/250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-199701/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c46 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-6069/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1038877/2000000) (δ := 12153/1000000000) (ψ := -109777/200000) 240 146
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t46 : ((-3579670597/50000000000 : ℚ) : ℝ) ≤ stT240 46 := by
  have hc : ((-48557/100000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3579670597/50000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-48557/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c47 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((288363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1195101/5000000) (δ := 6023/500000000) (ψ := -109777/200000) 240 147
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t47 : ((210291967681/2500000000000 : ℚ) : ℝ) ≤ stT240 47 := by
  have hc : ((144169/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210291967681/2500000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((144169/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c48 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((481309/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -685721/10000000) (δ := 377/31250000) (ψ := -109777/200000) 240 148
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t48 : ((1389346587/10000000000 : ℚ) : ℝ) ≤ stT240 48 := by
  have hc : ((120321/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1389346587/10000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((120321/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c49 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-1903/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1005541/2500000) (δ := 12171/1000000000) (ψ := -109777/200000) 240 149
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t49 : ((-1361071973/250000000000 : ℚ) : ℝ) ≤ stT240 49 := by
  have hc : ((-3811/100000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1361071973/250000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-3811/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c50 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-995181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -59441/78125) (δ := 97/8000000) (ψ := -109777/200000) 240 150
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t50 : ((-703734806717/5000000000000 : ℚ) : ℝ) ≤ stT240 50 := by
  have hc : ((-995231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-703734806717/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-995231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c51 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-138007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 534139/1250000) (δ := 97/8000000) (ψ := -109777/200000) 240 150
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t51 : ((-193318594017/10000000000000 : ℚ) : ℝ) ≤ stT240 51 := by
  have hc : ((-138057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193318594017/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-138057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c52 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((99627/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 216009/10000000) (δ := 12017/1000000000) (ψ := -109777/200000) 240 151
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t52 : ((276301617/2000000000 : ℚ) : ℝ) ≤ stT240 52 := by
  have hc : ((49811/50000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((276301617/2000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((49811/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c53 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-5439/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2031517/5000000) (δ := 12093/1000000000) (ψ := -109777/200000) 240 152
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t53 : ((-934738883/125000000000 : ℚ) : ℝ) ≤ stT240 53 := by
  have hc : ((-1361/25000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-934738883/125000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-1361/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c54 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-960861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3576113/5000000) (δ := 12093/1000000000) (ψ := -109777/200000) 240 152
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t54 : ((-326908648577/2500000000000 : ℚ) : ℝ) ≤ stT240 54 := by
  have hc : ((-960911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-326908648577/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-960911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c55 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((111157/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2453723/10000000) (δ := 61/5000000) (ψ := -109777/200000) 240 153
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t55 : ((149870503653/2000000000000 : ℚ) : ℝ) ≤ stT240 55 := by
  have hc : ((111147/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149870503653/2000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((111147/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c56 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((559299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2443141/10000000) (δ := 189/15625000) (ψ := -109777/200000) 240 154
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t56 : ((373663897097/5000000000000 : ℚ) : ℝ) ≤ stT240 56 := by
  have hc : ((559249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((373663897097/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((559249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c57 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-247921/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -470709/625000) (δ := 6007/500000000) (ψ := -109777/200000) 240 155
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t57 : ((-656792205111/5000000000000 : ℚ) : ℝ) ≤ stT240 57 := by
  have hc : ((-495867/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-656792205111/5000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-495867/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c58 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((397969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 362967/1250000) (δ := 6007/500000000) (ψ := -109777/200000) 240 155
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t58 : ((65311639227/1250000000000 : ℚ) : ℝ) ≤ stT240 58 := by
  have hc : ((397919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65311639227/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((397919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c59 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((131047/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2547587/10000000) (δ := 6061/500000000) (ψ := -109777/200000) 240 156
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t59 : ((341184748341/5000000000000 : ℚ) : ℝ) ≤ stT240 59 := by
  have hc : ((262069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((341184748341/5000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((262069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c60 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-247989/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7536673/10000000) (δ := 6061/500000000) (ψ := -109777/200000) 240 156
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t60 : ((-128067478597/1000000000000 : ℚ) : ℝ) ≤ stT240 60 := by
  have hc : ((-496003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128067478597/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-496003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c61 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((382899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1746289/10000000) (δ := 6087/500000000) (ψ := -109777/200000) 240 157
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t61 : ((15319363051/156250000000 : ℚ) : ℝ) ≤ stT240 61 := by
  have hc : ((191437/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15319363051/156250000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((191437/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c62 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-111123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2102687/5000000) (δ := 12067/1000000000) (ψ := -109777/200000) 240 158
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t62 : ((-70594966173/5000000000000 : ℚ) : ℝ) ≤ stT240 62 := by
  have hc : ((-111173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70594966173/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-111173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c63 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-553991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2697433/5000000) (δ := 12067/1000000000) (ψ := -109777/200000) 240 158
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t63 : ((-349013141581/5000000000000 : ℚ) : ℝ) ≤ stT240 63 := by
  have hc : ((-554041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-349013141581/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-554041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c64 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((940857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -864117/10000000) (δ := 12043/1000000000) (ψ := -109777/200000) 240 159
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t64 : ((940807/8000000 : ℚ) : ℝ) ≤ stT240 64 := by
  have hc : ((940807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((940807/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((940807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c65 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-608/625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -181739/250000) (δ := 243/20000000) (ψ := -109777/200000) 240 160
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t65 : ((-6033362759/50000000000 : ℚ) : ℝ) ≤ stT240 65 := by
  have hc : ((-19457/20000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6033362759/50000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-19457/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c66 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((22729/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94547/500000) (δ := 243/20000000) (ψ := -109777/200000) 240 160
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t66 : ((223804168023/2500000000000 : ℚ) : ℝ) ≤ stT240 66 := by
  have hc : ((363639/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((223804168023/2500000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((363639/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c67 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-17/50 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1198571/2500000) (δ := 6073/500000000) (ψ := -109777/200000) 240 161
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t67 : ((-1661749539/40000000000 : ℚ) : ℝ) ≤ stT240 67 := by
  have hc : ((-6801/20000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1661749539/40000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-6801/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c68 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-8383/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 511847/1250000) (δ := 6073/500000000) (ψ := -109777/200000) 240 161
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t68 : ((-40693869203/5000000000000 : ℚ) : ℝ) ≤ stT240 68 := by
  have hc : ((-33557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40693869203/5000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-33557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c69 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((208087/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2853907/10000000) (δ := 6019/500000000) (ψ := -109777/200000) 240 162
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t69 : ((62619275799/1250000000000 : ℚ) : ℝ) ≤ stT240 69 := by
  have hc : ((104031/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62619275799/1250000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((104031/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c70 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-337487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5779313/10000000) (δ := 6019/500000000) (ψ := -109777/200000) 240 162
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t70 : ((-50425516281/625000000000 : ℚ) : ℝ) ≤ stT240 70 := by
  have hc : ((-42189/62500 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50425516281/625000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-42189/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c71 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((105429/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -141789/1000000) (δ := 1509/125000000) (ψ := -109777/200000) 240 163
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t71 : ((500454866671/5000000000000 : ℚ) : ℝ) ≤ stT240 71 := by
  have hc : ((421691/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((500454866671/5000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((421691/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c72 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-58667/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 697389/1000000) (δ := 1509/125000000) (ψ := -109777/200000) 240 163
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t72 : ((-34571723177/312500000000 : ℚ) : ℝ) ≤ stT240 72 := by
  have hc : ((-469361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34571723177/312500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-469361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c73 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((983259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -458093/10000000) (δ := 12179/1000000000) (ψ := -109777/200000) 240 164
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t73 : ((1150758628899/10000000000000 : ℚ) : ℝ) ≤ stT240 73 := by
  have hc : ((983209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1150758628899/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((983209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c74 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-998231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7705267/10000000) (δ := 12179/1000000000) (ψ := -109777/200000) 240 164
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t74 : ((-1160478702037/10000000000000 : ℚ) : ℝ) ≤ stT240 74 := by
  have hc : ((-998281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1160478702037/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-998281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c75 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((999791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51163/10000000) (δ := 12117/1000000000) (ψ := -109777/200000) 240 165
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t75 : ((11544009327/100000000000 : ℚ) : ℝ) ≤ stT240 75 := by
  have hc : ((999741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11544009327/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((999741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c76 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-199667/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -96371/125000) (δ := 1201/100000000) (ψ := -109777/200000) 240 166
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t76 : ((-229045293483/2000000000000 : ℚ) : ℝ) ≤ stT240 76 := by
  have hc : ((-199677/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229045293483/2000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-199677/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c77 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((998573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6679/500000) (δ := 1201/100000000) (ψ := -109777/200000) 240 166
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t77 : ((227584360683/2000000000000 : ℚ) : ℝ) ≤ stT240 77 := by
  have hc : ((998523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227584360683/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((998523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c78 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-999963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7832343/10000000) (δ := 121/10000000) (ψ := -109777/200000) 240 167
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t78 : ((-566146359807/5000000000000 : ℚ) : ℝ) ≤ stT240 78 := by
  have hc : ((-1000013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-566146359807/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-1000013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c79 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((199429/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -188943/10000000) (δ := 121/10000000) (ψ := -109777/200000) 240 167
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t79 : ((224363724453/2000000000000 : ℚ) : ℝ) ≤ stT240 79 := by
  have hc : ((199419/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224363724453/2000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((199419/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c80 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-980411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7358337/10000000) (δ := 121/10000000) (ψ := -109777/200000) 240 167
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t80 : ((-548094366837/5000000000000 : ℚ) : ℝ) ≤ stT240 80 := by
  have hc : ((-980461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-548094366837/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-980461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c81 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((936441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -896127/10000000) (δ := 2439/200000000) (ψ := -109777/200000) 240 168
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t81 : ((1040434340401/10000000000000 : ℚ) : ℝ) ≤ stT240 81 := by
  have hc : ((936391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1040434340401/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((936391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c82 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-169957/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6465933/10000000) (δ := 2439/200000000) (ψ := -109777/200000) 240 168
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t82 : ((-46924319393/500000000000 : ℚ) : ℝ) ≤ stT240 82 := by
  have hc : ((-169967/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46924319393/500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-169967/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c83 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((352747/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -196919/1000000) (δ := 1511/125000000) (ψ := -109777/200000) 240 169
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t83 : ((96790620381/1250000000000 : ℚ) : ℝ) ≤ stT240 83 := by
  have hc : ((176361/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96790620381/1250000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((176361/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c84 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-246617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10433/20000) (δ := 3011/125000000) (ψ := -109777/200000) 240 169
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t84 : ((-13455430989/250000000000 : ℚ) : ℝ) ≤ stT240 84 := by
  have hc : ((-123321/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13455430989/250000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-123321/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c85 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((212839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3390793/10000000) (δ := 6011/500000000) (ψ := -109777/200000) 240 170
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t85 : ((57700503607/2500000000000 : ℚ) : ℝ) ≤ stT240 85 := by
  have hc : ((212789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57700503607/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((212789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c86 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((23957/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3626807/10000000) (δ := 6011/500000000) (ψ := -109777/200000) 240 170
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t86 : ((25822696669/2000000000000 : ℚ) : ℝ) ≤ stT240 86 := by
  have hc : ((23947/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25822696669/2000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((23947/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c87 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-468021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -643077/1250000) (δ := 12129/1000000000) (ψ := -109777/200000) 240 171
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t87 : ((-501825004023/10000000000000 : ℚ) : ℝ) ≤ stT240 87 := by
  have hc : ((-468071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-501825004023/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-468071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c88 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((774393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 428151/2500000) (δ := 12129/1000000000) (ψ := -109777/200000) 240 171
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t88 : ((825451961029/10000000000000 : ℚ) : ℝ) ≤ stT240 88 := by
  have hc : ((774343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((825451961029/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((774343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c89 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-48379/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -360783/500000) (δ := 12167/1000000000) (ψ := -109777/200000) 240 172
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t89 : ((-51284293237/500000000000 : ℚ) : ℝ) ≤ stT240 89 := by
  have hc : ((-96763/100000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51284293237/500000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-96763/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c90 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((122391/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1599/31250) (δ := 12167/1000000000) (ψ := -109777/200000) 240 172
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t90 : ((129004785897/1250000000000 : ℚ) : ℝ) ≤ stT240 90 := by
  have hc : ((489539/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129004785897/1250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((489539/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c91 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-768501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 611823/1000000) (δ := 24167/1000000000) (ψ := -109777/200000) 240 172
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t91 : ((-161132097007/2000000000000 : ℚ) : ℝ) ≤ stT240 91 := by
  have hc : ((-768551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161132097007/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-768551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c92 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((70057/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3032303/10000000) (δ := 12059/1000000000) (ψ := -109777/200000) 240 173
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t92 : ((18257260221/500000000000 : ℚ) : ℝ) ≤ stT240 92 := by
  have hc : ((70047/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18257260221/500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((70047/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c93 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((187977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3454237/10000000) (δ := 12059/1000000000) (ψ := -109777/200000) 240 173
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t93 : ((194871090577/10000000000000 : ℚ) : ℝ) ≤ stT240 93 := by
  have hc : ((187927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194871090577/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((187927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c94 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-691687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2918273/5000000) (δ := 12051/1000000000) (ψ := -109777/200000) 240 174
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t94 : ((-356736380007/5000000000000 : ℚ) : ℝ) ≤ stT240 94 := by
  have hc : ((-691737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-356736380007/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-691737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c95 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((244761/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 256357/5000000) (δ := 12051/1000000000) (ψ := -109777/200000) 240 174
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t95 : ((251106576533/2500000000000 : ℚ) : ℝ) ≤ stT240 95 := by
  have hc : ((489497/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((251106576533/2500000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((489497/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c96 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-911699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3397747/5000000) (δ := 12051/1000000000) (ψ := -109777/200000) 240 174
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t96 : ((-930550176129/10000000000000 : ℚ) : ℝ) ≤ stT240 96 := by
  have hc : ((-911749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-930550176129/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-911749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c97 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((236583/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2694789/10000000) (δ := 6079/500000000) (ψ := -109777/200000) 240 175
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t97 : ((60047054767/1250000000000 : ℚ) : ℝ) ≤ stT240 97 := by
  have hc : ((118279/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60047054767/1250000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((118279/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c98 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((186061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3459111/10000000) (δ := 6079/500000000) (ψ := -109777/200000) 240 175
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t98 : ((23487422959/1250000000000 : ℚ) : ℝ) ≤ stT240 98 := by
  have hc : ((186011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23487422959/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((186011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c99 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-155687/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6157413/10000000) (δ := 6069/500000000) (ψ := -109777/200000) 240 176
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t99 : ((-78240700743/1000000000000 : ℚ) : ℝ) ≤ stT240 99 := by
  have hc : ((-155697/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78240700743/1000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-155697/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c100 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((199741/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -127233/10000000) (δ := 6069/500000000) (ψ := -109777/200000) 240 176
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t100 : ((199730800269/2000000000000 : ℚ) : ℝ) ≤ stT240 100 := by
  have hc : ((199731/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199730800269/2000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((199731/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c101 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-693551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5843007/10000000) (δ := 6069/500000000) (ψ := -109777/200000) 240 176
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t101 : ((-345079675919/5000000000000 : ℚ) : ℝ) ≤ stT240 101 := by
  have hc : ((-693601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-345079675919/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-693601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c102 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-5317/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -494197/1250000) (δ := 12031/1000000000) (ψ := -109777/200000) 240 177
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t102 : ((-661171327/625000000000 : ℚ) : ℝ) ≤ stT240 102 := by
  have hc : ((-2671/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-661171327/625000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-2671/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c103 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((724813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 475021/2500000) (δ := 12031/1000000000) (ψ := -109777/200000) 240 177
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t103 : ((714130002027/10000000000000 : ℚ) : ℝ) ≤ stT240 103 := by
  have hc : ((724763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((714130002027/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((724763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c104 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-199607/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 962153/1250000) (δ := 12031/1000000000) (ψ := -109777/200000) 240 177
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t104 : ((-195740637477/2000000000000 : ℚ) : ℝ) ≤ stT240 104 := by
  have hc : ((-199617/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195740637477/2000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-199617/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c105 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((307813/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2269039/10000000) (δ := 12079/1000000000) (ψ := -109777/200000) 240 178
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t105 : ((750925773/12500000000 : ℚ) : ℝ) ≤ stT240 105 := by
  have hc : ((76947/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((750925773/12500000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((76947/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c106 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((101061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3418181/10000000) (δ := 12079/1000000000) (ψ := -109777/200000) 240 178
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t106 : ((4906737563/250000000000 : ℚ) : ℝ) ≤ stT240 106 := by
  have hc : ((25259/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4906737563/250000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((25259/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c107 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-887349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3327951/5000000) (δ := 12187/1000000000) (ψ := -109777/200000) 240 179
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t107 : ((-857881447063/10000000000000 : ℚ) : ℝ) ≤ stT240 107 := by
  have hc : ((-887399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-857881447063/10000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-887399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c108 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((181811/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -537231/5000000) (δ := 12187/1000000000) (ψ := -109777/200000) 240 179
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t108 : ((699752049/8000000000 : ℚ) : ℝ) ≤ stT240 108 := by
  have hc : ((181801/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((699752049/8000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((181801/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c109 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-26229/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2227749/5000000) (δ := 12187/1000000000) (ψ := -109777/200000) 240 179
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t109 : ((-100515323207/5000000000000 : ℚ) : ℝ) ≤ stT240 109 := by
  have hc : ((-104941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100515323207/5000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-104941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c110 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-336549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2886483/5000000) (δ := 12109/1000000000) (ψ := -109777/200000) 240 180
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t110 : ((-160455427881/2500000000000 : ℚ) : ℝ) ≤ stT240 110 := by
  have hc : ((-168287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160455427881/2500000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-168287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c111 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((990601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -171513/5000000) (δ := 12109/1000000000) (ψ := -109777/200000) 240 180
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t111 : ((940188415507/10000000000000 : ℚ) : ℝ) ≤ stT240 111 := by
  have hc : ((990551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((940188415507/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((990551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c112 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-26873/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2519067/5000000) (δ := 12109/1000000000) (ψ := -109777/200000) 240 180
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t112 : ((-12697786513/312500000000 : ℚ) : ℝ) ≤ stT240 112 := by
  have hc : ((-215009/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12697786513/312500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-215009/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c113 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-534381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5336429/10000000) (δ := 6001/500000000) (ψ := -109777/200000) 240 181
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t113 : ((-502750464751/10000000000000 : ℚ) : ℝ) ≤ stT240 113 := by
  have hc : ((-534431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-502750464751/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-534431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c114 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((999799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -50069/10000000) (δ := 6001/500000000) (ψ := -109777/200000) 240 181
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t114 : ((187269983433/2000000000000 : ℚ) : ℝ) ≤ stT240 114 := by
  have hc : ((999749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187269983433/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((999749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c115 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-484039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5190151/10000000) (δ := 6001/500000000) (ψ := -109777/200000) 240 181
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t115 : ((-90283082589/2000000000000 : ℚ) : ℝ) ≤ stT240 115 := by
  have hc : ((-484089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90283082589/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-484089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c116 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-529837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1330753/2500000) (δ := 3027/250000000) (ψ := -109777/200000) 240 182
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t116 : ((-491987892099/10000000000000 : ℚ) : ℝ) ≤ stT240 116 := by
  have hc : ((-529887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-491987892099/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-529887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c117 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((498807/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43183/2500000) (δ := 3027/250000000) (ψ := -109777/200000) 240 182
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t117 : ((461123959/5000000000 : ℚ) : ℝ) ≤ stT240 117 := by
  have hc : ((249391/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((461123959/5000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((249391/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c118 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-97971/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 616711/1250000) (δ := 3027/250000000) (ψ := -109777/200000) 240 182
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t118 : ((-7216092841/200000000000 : ℚ) : ℝ) ≤ stT240 118 := by
  have hc : ((-195967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7216092841/200000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-195967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c119 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-654561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1427749/2500000) (δ := 3047/250000000) (ψ := -109777/200000) 240 183
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t119 : ((-600081249089/10000000000000 : ℚ) : ℝ) ≤ stT240 119 := by
  have hc : ((-654611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-600081249089/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-654611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c120 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((962151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21563/312500) (δ := 3047/250000000) (ψ := -109777/200000) 240 183
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t120 : ((87827313987/1000000000000 : ℚ) : ℝ) ≤ stT240 120 := by
  have hc : ((962101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87827313987/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((962101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c121 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-144403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 268079/625000) (δ := 3047/250000000) (ψ := -109777/200000) 240 183
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t121 : ((-131320922223/10000000000000 : ℚ) : ℝ) ≤ stT240 121 := by
  have hc : ((-144453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131320922223/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-144453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c122 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-852821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6480399/10000000) (δ := 151/12500000) (ψ := -109777/200000) 240 184
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t122 : ((-386076791409/5000000000000 : ℚ) : ℝ) ≤ stT240 122 := by
  have hc : ((-852871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-386076791409/5000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-852871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c123 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((201569/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1582419/10000000) (δ := 151/12500000) (ψ := -109777/200000) 240 184
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t123 : ((363474495597/5000000000000 : ℚ) : ℝ) ≤ stT240 123 := by
  have hc : ((403113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((363474495597/5000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((403113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c124 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((128751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3275901/10000000) (δ := 151/12500000) (ψ := -109777/200000) 240 184
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t124 : ((28899823719/1250000000000 : ℚ) : ℝ) ≤ stT240 124 := by
  have hc : ((64363/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28899823719/1250000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((64363/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c125 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-248837/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3806371/5000000) (δ := 1203/100000000) (ψ := -109777/200000) 240 185
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t125 : ((-111288980293/1250000000000 : ℚ) : ℝ) ≤ stT240 125 := by
  have hc : ((-497699/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111288980293/1250000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-497699/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c126 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((42419/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1415911/5000000) (δ := 1203/100000000) (ψ := -109777/200000) 240 185
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t126 : ((1889268009/50000000000 : ℚ) : ℝ) ≤ stT240 126 := by
  have hc : ((21207/50000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1889268009/50000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((21207/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c127 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((180433/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 955619/5000000) (δ := 1203/100000000) (ψ := -109777/200000) 240 185
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t127 : ((80048606599/1250000000000 : ℚ) : ℝ) ≤ stT240 127 := by
  have hc : ((360841/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80048606599/1250000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((360841/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c128 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-880097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3308579/5000000) (δ := 1203/100000000) (ψ := -109777/200000) 240 185
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t128 : ((-194486962737/2500000000000 : ℚ) : ℝ) ≤ stT240 128 := by
  have hc : ((-880147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194486962737/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-880147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c129 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-19651/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -884297/2000000) (δ := 12137/1000000000) (ψ := -109777/200000) 240 186
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t129 : ((-2163268107/125000000000 : ℚ) : ℝ) ≤ stT240 129 := by
  have hc : ((-2457/12500 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2163268107/125000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-2457/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c130 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((15569/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42343/2000000) (δ := 12137/1000000000) (ψ := -109777/200000) 240 186
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t130 : ((218467692807/2500000000000 : ℚ) : ℝ) ≤ stT240 130 := by
  have hc : ((498183/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218467692807/2500000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((498183/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c131 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-345701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 961891/2000000) (δ := 12137/1000000000) (ψ := -109777/200000) 240 186
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t131 : ((-60416875491/2000000000000 : ℚ) : ℝ) ≤ stT240 131 := by
  have hc : ((-345751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60416875491/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-345751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c132 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-205299/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6335749/10000000) (δ := 12159/1000000000) (ψ := -109777/200000) 240 187
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t132 : ((-357401742347/5000000000000 : ℚ) : ℝ) ≤ stT240 132 := by
  have hc : ((-410623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-357401742347/5000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-410623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c133 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((749843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1807429/10000000) (δ := 12159/1000000000) (ψ := -109777/200000) 240 187
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t133 : ((650152258437/10000000000000 : ℚ) : ℝ) ≤ stT240 133 := by
  have hc : ((749793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((650152258437/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((749793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c134 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((237961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2686961/10000000) (δ := 24159/1000000000) (ψ := -109777/200000) 240 187
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t134 : ((3211645257/78125000000 : ℚ) : ℝ) ≤ stT240 134 := by
  have hc : ((14871/31250 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3211645257/78125000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((14871/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c135 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-15006/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7147931/10000000) (δ := 12159/1000000000) (ψ := -109777/200000) 240 187
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t135 : ((-413305003871/5000000000000 : ℚ) : ℝ) ≤ stT240 135 := by
  have hc : ((-480217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-413305003871/5000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-480217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c136 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-81901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1032993/2500000) (δ := 3013/250000000) (ψ := -109777/200000) 240 188
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t136 : ((-70272408843/10000000000000 : ℚ) : ℝ) ≤ stT240 136 := by
  have hc : ((-81951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70272408843/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-81951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c137 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((994443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 32961/1250000) (δ := 3013/250000000) (ψ := -109777/200000) 240 188
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t137 : ((849566620301/10000000000000 : ℚ) : ℝ) ≤ stT240 137 := by
  have hc : ((994393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((849566620301/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((994393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c138 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-138239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1156827/2500000) (δ := 3013/250000000) (ψ := -109777/200000) 240 188
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t138 : ((-14712274731/625000000000 : ℚ) : ℝ) ≤ stT240 138 := by
  have hc : ((-17283/62500 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14712274731/625000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-17283/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c139 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-903811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -269939/400000) (δ := 6029/500000000) (ψ := -109777/200000) 240 189
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t139 : ((-766644957729/10000000000000 : ℚ) : ℝ) ≤ stT240 139 := by
  have hc : ((-903861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-766644957729/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-903861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c140 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((278947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19579/80000) (δ := 6029/500000000) (ψ := -109777/200000) 240 189
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t140 : ((58933010997/1250000000000 : ℚ) : ℝ) ≤ stT240 140 := by
  have hc : ((139461/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58933010997/1250000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((139461/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c141 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((74569/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 364613/2000000) (δ := 6029/500000000) (ψ := -109777/200000) 240 189
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t141 : ((15698536791/250000000000 : ℚ) : ℝ) ≤ stT240 141 := by
  have hc : ((18641/25000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15698536791/250000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((18641/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c142 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-754281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1212677/2000000) (δ := 6029/500000000) (ψ := -109777/200000) 240 189
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t142 : ((-316510498621/5000000000000 : ℚ) : ℝ) ≤ stT240 142 := by
  have hc : ((-754331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-316510498621/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-754331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c143 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-7087/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2717009/5000000) (δ := 6083/500000000) (ψ := -109777/200000) 240 190
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t143 : ((-47415814343/1000000000000 : ℚ) : ℝ) ≤ stT240 143 := by
  have hc : ((-56701/100000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47415814343/1000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-56701/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c144 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((438517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -626429/5000000) (δ := 6083/500000000) (ψ := -109777/200000) 240 190
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t144 : ((91352463459/1250000000000 : ℚ) : ℝ) ≤ stT240 144 := by
  have hc : ((109623/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91352463459/1250000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((109623/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c145 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((49943/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1449721/5000000) (δ := 6083/500000000) (ψ := -109777/200000) 240 190
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t145 : ((82940347569/2500000000000 : ℚ) : ℝ) ≤ stT240 145 := by
  have hc : ((199747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82940347569/2500000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((199747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c146 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-118161/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3511591/5000000) (δ := 6083/500000000) (ψ := -109777/200000) 240 190
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t146 : ((-195591850207/2500000000000 : ℚ) : ℝ) ≤ stT240 146 := by
  have hc : ((-472669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195591850207/2500000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-472669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c147 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-261813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2294621/5000000) (δ := 1213/100000000) (ψ := -109777/200000) 240 191
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t147 : ((-215981198181/10000000000000 : ℚ) : ℝ) ≤ stT240 147 := by
  have hc : ((-261863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215981198181/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-261863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c148 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((122291/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -260711/5000000) (δ := 1213/100000000) (ψ := -109777/200000) 240 191
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t148 : ((201034661583/2500000000000 : ℚ) : ℝ) ≤ stT240 148 := by
  have hc : ((489139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201034661583/2500000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((489139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c149 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((81229/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1759519/5000000) (δ := 1213/100000000) (ψ := -109777/200000) 240 191
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t149 : ((16631208531/1250000000000 : ℚ) : ℝ) ≤ stT240 149 := by
  have hc : ((20301/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16631208531/1250000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((20301/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c150 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-991737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3766189/5000000) (δ := 1213/100000000) (ψ := -109777/200000) 240 191
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t150 : ((-809791110139/10000000000000 : ℚ) : ℝ) ≤ stT240 150 := by
  have hc : ((-991787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-809791110139/10000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-991787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c151 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-52271/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -167553/400000) (δ := 12023/1000000000) (ψ := -109777/200000) 240 192
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t151 : ((-5319738693/625000000000 : ℚ) : ℝ) ≤ stT240 151 := by
  have hc : ((-6537/62500 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5319738693/625000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-6537/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c152 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((995829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -45681/2000000) (δ := 12023/1000000000) (ψ := -109777/200000) 240 192
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t152 : ((807683317353/10000000000000 : ℚ) : ℝ) ≤ stT240 152 := by
  have hc : ((995779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((807683317353/10000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((995779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c153 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((88267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 741207/2000000) (δ := 12023/1000000000) (ψ := -109777/200000) 240 192
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t153 : ((17829802521/2500000000000 : ℚ) : ℝ) ≤ stT240 153 := by
  have hc : ((88217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17829802521/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((88217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c154 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-995429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1522971/2000000) (δ := 12023/1000000000) (ψ := -109777/200000) 240 192
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t154 : ((-802179874217/10000000000000 : ℚ) : ℝ) ≤ stT240 154 := by
  have hc : ((-995479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-802179874217/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-995479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c155 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-56403/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -526201/1250000) (δ := 12087/1000000000) (ψ := -109777/200000) 240 193
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t155 : ((-566551227/62500000000 : ℚ) : ℝ) ≤ stT240 155 := by
  have hc : ((-14107/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-566551227/62500000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-14107/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c156 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((247539/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87767/2500000) (δ := 12087/1000000000) (ψ := -109777/200000) 240 193
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t156 : ((619311303/7812500000 : ℚ) : ℝ) ≤ stT240 156 := by
  have hc : ((495053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((619311303/7812500000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((495053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c157 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((88369/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 870703/2500000) (δ := 12087/1000000000) (ψ := -109777/200000) 240 193
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t157 : ((4406631849/312500000000 : ℚ) : ℝ) ≤ stT240 157 := by
  have hc : ((11043/62500 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4406631849/312500000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((11043/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c158 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-97487/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1823083/2500000) (δ := 12087/1000000000) (ψ := -109777/200000) 240 193
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t158 : ((-9695067567/125000000000 : ℚ) : ℝ) ≤ stT240 158 := by
  have hc : ((-24373/25000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9695067567/125000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-24373/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c159 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-55511/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4630111/10000000) (δ := 6097/500000000) (ψ := -109777/200000) 240 194
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t159 : ((-11007760023/500000000000 : ℚ) : ℝ) ≤ stT240 159 := by
  have hc : ((-55521/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11007760023/500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-55521/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c160 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((940281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -868351/10000000) (δ := 6097/500000000) (ψ := -109777/200000) 240 194
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t160 : ((743317481439/10000000000000 : ℚ) : ℝ) ≤ stT240 160 := by
  have hc : ((940231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((743317481439/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((940231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c161 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((410331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2869949/10000000) (δ := 6097/500000000) (ψ := -109777/200000) 240 194
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t161 : ((32334655891/1000000000000 : ℚ) : ℝ) ≤ stT240 161 := by
  have hc : ((410281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32334655891/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((410281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c162 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-436973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6585149/10000000) (δ := 6097/500000000) (ψ := -109777/200000) 240 194
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t162 : ((-6866768073/100000000000 : ℚ) : ℝ) ≤ stT240 162 := by
  have hc : ((-218499/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6866768073/100000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-218499/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c163 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-17681/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -217219/400000) (δ := 12101/1000000000) (ψ := -109777/200000) 240 195
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t163 : ((-221600985381/5000000000000 : ℚ) : ℝ) ≤ stT240 163 := by
  have hc : ((-282921/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221600985381/5000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-282921/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c164 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((47629/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -352151/2000000) (δ := 12101/1000000000) (ψ := -109777/200000) 240 195
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t164 : ((74379043519/1250000000000 : ℚ) : ℝ) ≤ stT240 164 := by
  have hc : ((381007/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74379043519/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((381007/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c165 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((364253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 377329/2000000) (δ := 12101/1000000000) (ψ := -109777/200000) 240 195
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t165 : ((35443846193/625000000000 : ℚ) : ℝ) ≤ stT240 165 := by
  have hc : ((91057/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35443846193/625000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((91057/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c166 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-592383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 220481/400000) (δ := 12101/1000000000) (ψ := -109777/200000) 240 195
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t166 : ((-459817465383/10000000000000 : ℚ) : ℝ) ≤ stT240 166 := by
  have hc : ((-592433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-459817465383/10000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-592433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c167 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-875329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3296139/5000000) (δ := 12009/1000000000) (ψ := -109777/200000) 240 196
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t167 : ((-10584207489/156250000000 : ℚ) : ℝ) ≤ stT240 167 := by
  have hc : ((-875379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10584207489/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-875379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c168 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((71709/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1505109/5000000) (δ := 12009/1000000000) (ψ := -109777/200000) 240 196
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t168 : ((13829231421/500000000000 : ℚ) : ℝ) ≤ stT240 168 := by
  have hc : ((71699/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13829231421/500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((71699/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c169 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((6099/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 275331/5000000) (δ := 12009/1000000000) (ψ := -109777/200000) 240 196
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t169 : ((7506069417/100000000000 : ℚ) : ℝ) ≤ stT240 169 := by
  have hc : ((97579/100000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7506069417/100000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((97579/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c170 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-1307/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2045241/5000000) (δ := 12009/1000000000) (ψ := -109777/200000) 240 196
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t170 : ((-50159511/10000000000 : ℚ) : ℝ) ≤ stT240 170 := by
  have hc : ((-327/5000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50159511/10000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-327/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c171 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-124403/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3804771/5000000) (δ := 12009/1000000000) (ψ := -109777/200000) 240 196
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t171 : ((-4756912083/62500000000 : ℚ) : ℝ) ≤ stT240 171 := by
  have hc : ((-497637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4756912083/62500000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-497637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c172 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-132959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4599881/10000000) (δ := 3029/250000000) (ψ := -109777/200000) 240 197
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t172 : ((-12674921139/625000000000 : ℚ) : ℝ) ≤ stT240 172 := by
  have hc : ((-16623/62500 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12674921139/625000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-16623/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c173 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((450517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1121621/10000000) (δ := 3029/250000000) (ψ := -109777/200000) 240 197
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t173 : ((17125115511/250000000000 : ℚ) : ℝ) ≤ stT240 173 := by
  have hc : ((112623/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17125115511/250000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((112623/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c174 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((148527/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2336599/10000000) (δ := 3029/250000000) (ψ := -109777/200000) 240 197
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t174 : ((112588545421/2500000000000 : ℚ) : ℝ) ≤ stT240 174 := by
  have hc : ((297029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112588545421/2500000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((297029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c175 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-134741/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5775019/10000000) (δ := 3029/250000000) (ψ := -109777/200000) 240 197
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t175 : ((-101862188679/2000000000000 : ℚ) : ℝ) ≤ stT240 175 := by
  have hc : ((-134751/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101862188679/2000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-134751/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c176 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-53737/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1302829/2000000) (δ := 609/50000000) (ψ := -109777/200000) 240 198
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t176 : ((-324065421459/5000000000000 : ℚ) : ℝ) ≤ stT240 176 := by
  have hc : ((-429921/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324065421459/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-429921/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c177 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((319243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -622933/2000000) (δ := 609/50000000) (ψ := -109777/200000) 240 198
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t177 : ((119960070839/5000000000000 : ℚ) : ℝ) ≤ stT240 177 := by
  have hc : ((319193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119960070839/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((319193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c178 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((994361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 53123/2000000) (δ := 609/50000000) (ψ := -109777/200000) 240 198
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t178 : ((745266918141/10000000000000 : ℚ) : ℝ) ≤ stT240 178 := by
  have hc : ((994311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((745266918141/10000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((994311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c179 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((119711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 725399/2000000) (δ := 609/50000000) (ψ := -109777/200000) 240 198
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t179 : ((17887763907/2000000000000 : ℚ) : ℝ) ≤ stT240 179 := by
  have hc : ((119661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17887763907/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((119661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c180 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-938079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1393919/2000000) (δ := 609/50000000) (ψ := -109777/200000) 240 198
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t180 : ((-174810019731/2500000000000 : ℚ) : ℝ) ≤ stT240 180 := by
  have hc : ((-938129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174810019731/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-938129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c181 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-140107/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -676781/1250000) (δ := 12073/1000000000) (ψ := -109777/200000) 240 199
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t181 : ((-41660049501/1000000000000 : ℚ) : ℝ) ≤ stT240 181 := by
  have hc : ((-280239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41660049501/1000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-280239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c182 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((664931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -263561/1250000) (δ := 12073/1000000000) (ψ := -109777/200000) 240 199
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t182 : ((492842376369/10000000000000 : ℚ) : ℝ) ≤ stT240 182 := by
  have hc : ((664881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((492842376369/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((664881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c183 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((222701/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 294803/2500000) (δ := 12073/1000000000) (ψ := -109777/200000) 240 199
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t183 : ((329232031317/5000000000000 : ℚ) : ℝ) ≤ stT240 183 := by
  have hc : ((445377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((329232031317/5000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((445377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c184 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-207279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1112243/2500000) (δ := 12073/1000000000) (ψ := -109777/200000) 240 199
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t184 : ((-15284501209/1000000000000 : ℚ) : ℝ) ≤ stT240 184 := by
  have hc : ((-207329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15284501209/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-207329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c185 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-998129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 962629/1250000) (δ := 12073/1000000000) (ψ := -109777/200000) 240 199
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t185 : ((-146775234697/2000000000000 : ℚ) : ℝ) ≤ stT240 185 := by
  have hc : ((-998179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146775234697/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-998179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c186 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-13271/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4772451/10000000) (δ := 12037/1000000000) (ψ := -109777/200000) 240 200
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t186 : ((-2433060357/100000000000 : ℚ) : ℝ) ≤ stT240 186 := by
  have hc : ((-13273/40000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2433060357/100000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-13273/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c187 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((50791/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1555251/10000000) (δ := 12037/1000000000) (ψ := -109777/200000) 240 200
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t187 : ((37139750927/625000000000 : ℚ) : ℝ) ≤ stT240 187 := by
  have hc : ((406303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37139750927/625000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((406303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c188 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((791283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1644729/10000000) (δ := 12037/1000000000) (ψ := -109777/200000) 240 200
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t188 : ((144266304123/2500000000000 : ℚ) : ℝ) ≤ stT240 188 := by
  have hc : ((791233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144266304123/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((791233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c189 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-352573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4827789/10000000) (δ := 12037/1000000000) (ψ := -109777/200000) 240 200
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t189 : ((-256495501839/10000000000000 : ℚ) : ℝ) ≤ stT240 189 := by
  have hc : ((-352623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-256495501839/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-352623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c190 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-31201/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3856987/5000000) (δ := 2429/200000000) (ψ := -109777/200000) 240 201
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t190 : ((-362187862957/5000000000000 : ℚ) : ℝ) ≤ stT240 190 := by
  have hc : ((-499241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-362187862957/5000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-499241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c191 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-50437/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2282167/5000000) (δ := 2429/200000000) (ψ := -109777/200000) 240 201
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t191 : ((-1460087521/80000000000 : ℚ) : ℝ) ≤ stT240 191 := by
  have hc : ((-50447/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1460087521/80000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-50447/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c192 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((840561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -715597/5000000) (δ := 2429/200000000) (ψ := -109777/200000) 240 201
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t192 : ((606585862057/10000000000000 : ℚ) : ℝ) ≤ stT240 192 := by
  have hc : ((840511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((606585862057/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((840511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c193 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((19529/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 842843/5000000) (δ := 2429/200000000) (ψ := -109777/200000) 240 201
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t193 : ((11245093893/200000000000 : ℚ) : ℝ) ≤ stT240 193 := by
  have hc : ((78111/100000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11245093893/200000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((78111/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c194 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-67413/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2393243/5000000) (δ := 2429/200000000) (ψ := -109777/200000) 240 201
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t194 : ((-48406949657/2000000000000 : ℚ) : ℝ) ≤ stT240 194 := by
  have hc : ((-67423/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48406949657/2000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-67423/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c195 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-124997/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3918319/5000000) (δ := 12151/1000000000) (ψ := -109777/200000) 240 202
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t195 : ((-71613361899/1000000000000 : ℚ) : ℝ) ≤ stT240 195 := by
  have hc : ((-500013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71613361899/1000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-500013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c196 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-65987/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2383789/5000000) (δ := 12151/1000000000) (ψ := -109777/200000) 240 202
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t196 : ((-23570366571/1000000000000 : ℚ) : ℝ) ≤ stT240 196 := by
  have hc : ((-65997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23570366571/1000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-65997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c197 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((774009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -857059/5000000) (δ := 12151/1000000000) (ψ := -109777/200000) 240 202
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t197 : ((55142256873/1000000000000 : ℚ) : ℝ) ≤ stT240 197 := by
  have hc : ((773959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55142256873/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((773959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c198 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((863037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 661931/5000000) (δ := 12151/1000000000) (ψ := -109777/200000) 240 202
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t198 : ((613298108303/10000000000000 : ℚ) : ℝ) ≤ stT240 198 := by
  have hc : ((862987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((613298108303/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((862987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c199 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-83517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2173271/5000000) (δ := 12151/1000000000) (ψ := -109777/200000) 240 202
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t199 : ((-14805355011/1250000000000 : ℚ) : ℝ) ≤ stT240 199 := by
  have hc : ((-41771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14805355011/1250000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-41771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c200 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-980071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3677021/5000000) (δ := 12151/1000000000) (ψ := -109777/200000) 240 202
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t200 : ((-693050419947/10000000000000 : ℚ) : ℝ) ≤ stT240 200 := by
  have hc : ((-980121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-693050419947/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-980121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c201 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-8481/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5361361/10000000) (δ := 3011/250000000) (ψ := -109777/200000) 240 203
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t201 : ((-95721447641/2500000000000 : ℚ) : ℝ) ≤ stT240 201 := by
  have hc : ((-271417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95721447641/2500000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-271417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c202 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((144709/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2383741/10000000) (δ := 3011/250000000) (ψ := -109777/200000) 240 203
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t202 : ((203616046621/5000000000000 : ℚ) : ℝ) ≤ stT240 202 := by
  have hc : ((289393/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203616046621/5000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((289393/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c203 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((486639/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 579239/10000000) (δ := 3011/250000000) (ψ := -109777/200000) 240 203
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t203 : ((85383968817/1250000000000 : ℚ) : ℝ) ≤ stT240 203 := by
  have hc : ((243307/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85383968817/1250000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((243307/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c204 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((79531/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3527639/10000000) (δ := 3011/250000000) (ψ := -109777/200000) 240 203
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t204 : ((1391633271/125000000000 : ℚ) : ℝ) ≤ stT240 204 := by
  have hc : ((39753/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1391633271/125000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((39753/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c205 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-424439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6461639/10000000) (δ := 3011/250000000) (ψ := -109777/200000) 240 203
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t205 : ((-18528675999/312500000000 : ℚ) : ℝ) ≤ stT240 205 := by
  have hc : ((-26529/31250 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18528675999/312500000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-26529/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c206 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-819103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1581651/2500000) (δ := 6033/500000000) (ψ := -109777/200000) 240 204
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t206 : ((-285365873151/5000000000000 : ℚ) : ℝ) ≤ stT240 206 := by
  have hc : ((-819153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285365873151/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-819153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c207 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((201/1000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -855261/2500000) (δ := 6033/500000000) (ψ := -109777/200000) 240 204
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t207 : ((349174739/25000000000 : ℚ) : ℝ) ≤ stT240 207 := by
  have hc : ((4019/20000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((349174739/25000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((4019/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c208 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((977657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -66183/1250000) (δ := 6033/500000000) (ψ := -109777/200000) 240 204
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t208 : ((5422786029/80000000000 : ℚ) : ℝ) ≤ stT240 208 := by
  have hc : ((977607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5422786029/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((977607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c209 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((590351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73383/312500) (δ := 6033/500000000) (ψ := -109777/200000) 240 204
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t209 : ((204159732957/5000000000000 : ℚ) : ℝ) ≤ stT240 209 := by
  have hc : ((590301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204159732957/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((590301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c210 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-1967/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1303059/2500000) (δ := 6033/500000000) (ψ := -109777/200000) 240 204
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t210 : ((-848436147/25000000000 : ℚ) : ℝ) ≤ stT240 210 := by
  have hc : ((-2459/5000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-848436147/25000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-2459/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c211 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-24913/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7645367/10000000) (δ := 12173/1000000000) (ψ := -109777/200000) 240 205
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t211 : ((-68606768853/1000000000000 : ℚ) : ℝ) ≤ stT240 211 := by
  have hc : ((-99657/100000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68606768853/1000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-99657/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c212 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-69069/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4808507/10000000) (δ := 12173/1000000000) (ψ := -109777/200000) 240 205
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t212 : ((-47443664437/2000000000000 : ℚ) : ℝ) ≤ stT240 212 := by
  have hc : ((-69079/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47443664437/2000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-69079/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c213 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((43813/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1984967/10000000) (δ := 12173/1000000000) (ψ := -109777/200000) 240 205
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t213 : ((60036001263/1250000000000 : ℚ) : ℝ) ≤ stT240 213 := by
  have hc : ((350479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60036001263/1250000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((350479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c214 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((472997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 825373/10000000) (δ := 12173/1000000000) (ψ := -109777/200000) 240 205
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t214 : ((16165828231/250000000000 : ℚ) : ℝ) ≤ stT240 214 := by
  have hc : ((118243/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16165828231/250000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((118243/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c215 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((60733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3622573/10000000) (δ := 12173/1000000000) (ψ := -109777/200000) 240 205
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t215 : ((5175311469/625000000000 : ℚ) : ℝ) ≤ stT240 215 := by
  have hc : ((15177/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5175311469/625000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((15177/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c216 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-837083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6406813/10000000) (δ := 12173/1000000000) (ψ := -109777/200000) 240 205
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t216 : ((-284798506531/5000000000000 : ℚ) : ℝ) ≤ stT240 216 := by
  have hc : ((-837133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284798506531/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-837133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c217 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-34519/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6529811/10000000) (δ := 12123/1000000000) (ψ := -109777/200000) 240 206
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t217 : ((-4686881649/80000000000 : ℚ) : ℝ) ≤ stT240 217 := by
  have hc : ((-34521/40000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4686881649/80000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-34521/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c218 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((1557/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3771191/10000000) (δ := 12123/1000000000) (ψ := -109777/200000) 240 206
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t218 : ((842948911/200000000000 : ℚ) : ℝ) ≤ stT240 218 := by
  have hc : ((6223/100000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((842948911/200000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((6223/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c219 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((458547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1025171/10000000) (δ := 12123/1000000000) (ψ := -109777/200000) 240 206
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t219 : ((154920140357/2500000000000 : ℚ) : ℝ) ≤ stT240 219 := by
  have hc : ((229261/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154920140357/2500000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((229261/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c220 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((775479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1708309/10000000) (δ := 12123/1000000000) (ψ := -109777/200000) 240 206
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t220 : ((522793456371/10000000000000 : ℚ) : ℝ) ≤ stT240 220 := by
  have hc : ((775429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((522793456371/10000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((775429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c221 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-1597/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4429429/10000000) (δ := 12123/1000000000) (ψ := -109777/200000) 240 206
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t221 : ((-5372639251/400000000000 : ℚ) : ℝ) ≤ stT240 221 := by
  have hc : ((-7987/40000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5372639251/400000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-7987/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c222 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-959291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7138189/10000000) (δ := 12123/1000000000) (ψ := -109777/200000) 240 206
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t222 : ((-643868427537/10000000000000 : ℚ) : ℝ) ≤ stT240 222 := by
  have hc : ((-959341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-643868427537/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-959341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c223 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-351091/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2936567/5000000) (δ := 2403/200000000) (ψ := -109777/200000) 240 207
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t223 : ((-1175624147/25000000000 : ℚ) : ℝ) ≤ stT240 223 := by
  have hc : ((-87779/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1175624147/25000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-87779/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c224 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((145549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1594277/5000000) (δ := 2403/200000000) (ψ := -109777/200000) 240 207
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t224 : ((24308074293/1250000000000 : ℚ) : ℝ) ≤ stT240 224 := by
  have hc : ((36381/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24308074293/1250000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((36381/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c225 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((489391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -257957/5000000) (δ := 2403/200000000) (ψ := -109777/200000) 240 207
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t225 : ((81560918439/1250000000000 : ℚ) : ℝ) ≤ stT240 225 := by
  have hc : ((244683/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81560918439/1250000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((244683/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c226 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((81751/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 134051/625000) (δ := 4803/200000000) (ψ := -109777/200000) 240 207
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t226 : ((21750316101/500000000000 : ℚ) : ℝ) ≤ stT240 226 := by
  have hc : ((326979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21750316101/500000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((326979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c227 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-84959/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2396923/5000000) (δ := 2403/200000000) (ψ := -109777/200000) 240 207
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t227 : ((-28198811933/1250000000000 : ℚ) : ℝ) ≤ stT240 227 := by
  have hc : ((-169943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28198811933/1250000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-169943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c228 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-197147/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3715603/5000000) (δ := 2403/200000000) (ψ := -109777/200000) 240 207
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t228 : ((-130570574919/2000000000000 : ℚ) : ℝ) ≤ stT240 228 := by
  have hc : ((-197157/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130570574919/2000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-197157/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c229 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-318103/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5650917/10000000) (δ := 2419/200000000) (ψ := -109777/200000) 240 208
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t229 : ((-13139064177/312500000000 : ℚ) : ℝ) ≤ stT240 229 := by
  have hc : ((-19883/31250 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13139064177/312500000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-19883/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c230 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((174349/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3036537/10000000) (δ := 2419/200000000) (ψ := -109777/200000) 240 208
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t230 : ((1436821989/62500000000 : ℚ) : ℝ) ≤ stT240 230 := by
  have hc : ((43581/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1436821989/62500000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((43581/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c231 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((246251/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -433497/10000000) (δ := 2419/200000000) (ψ := -109777/200000) 240 208
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t231 : ((324025734627/5000000000000 : ℚ) : ℝ) ≤ stT240 231 := by
  have hc : ((492477/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((324025734627/5000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((492477/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c232 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((649929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2158263/10000000) (δ := 2419/200000000) (ψ := -109777/200000) 240 208
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t232 : ((106666589907/2500000000000 : ℚ) : ℝ) ≤ stT240 232 := by
  have hc : ((649879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106666589907/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((649879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c233 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-159547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4738923/10000000) (δ := 2419/200000000) (ψ := -109777/200000) 240 208
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t233 : ((-13067390973/625000000000 : ℚ) : ℝ) ≤ stT240 233 := by
  have hc : ((-39893/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13067390973/625000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-39893/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c234 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-488147/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7308543/10000000) (δ := 2419/200000000) (ψ := -109777/200000) 240 208
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t234 : ((-79782072003/1250000000000 : ℚ) : ℝ) ≤ stT240 234 := by
  have hc : ((-122043/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79782072003/1250000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-122043/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c235 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-692909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5840781/10000000) (δ := 12201/1000000000) (ψ := -109777/200000) 240 209
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t235 : ((-452037251511/10000000000000 : ℚ) : ℝ) ≤ stT240 235 := by
  have hc : ((-692959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-452037251511/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-692959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c236 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((125443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3293001/10000000) (δ := 12201/1000000000) (ψ := -109777/200000) 240 209
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t236 : ((637813239/39062500000 : ℚ) : ℝ) ≤ stT240 236 := by
  have hc : ((62709/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((637813239/39062500000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((62709/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c237 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((477311/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -756021/10000000) (δ := 12201/1000000000) (ψ := -109777/200000) 240 209
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t237 : ((155015094867/2500000000000 : ℚ) : ℝ) ≤ stT240 237 := by
  have hc : ((238643/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155015094867/2500000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((238643/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c238 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((759591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1770279/10000000) (δ := 12201/1000000000) (ψ := -109777/200000) 240 209
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t238 : ((492336754823/10000000000000 : ℚ) : ℝ) ≤ stT240 238 := by
  have hc : ((759541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((492336754823/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((759541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c239 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-71559/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4286019/10000000) (δ := 12201/1000000000) (ψ := -109777/200000) 240 209
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t239 : ((-1446996739/156250000000 : ℚ) : ℝ) ≤ stT240 239 := by
  have hc : ((-2237/15625 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1446996739/156250000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-2237/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c240 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-455501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6791259/10000000) (δ := 12201/1000000000) (ψ := -109777/200000) 240 209
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t240 : ((-73510280487/1250000000000 : ℚ) : ℝ) ≤ stT240 240 := by
  have hc : ((-227763/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73510280487/1250000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-227763/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c241 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-84037/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -401369/625000) (δ := 6047/500000000) (ψ := -109777/200000) 240 210
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t241 : ((-27068121297/500000000000 : ℚ) : ℝ) ≤ stT240 241 := by
  have hc : ((-42021/50000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27068121297/500000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-42021/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c242 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-4173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -246089/625000) (δ := 6047/500000000) (ψ := -109777/200000) 240 210
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t242 : ((-108585999/400000000000 : ℚ) : ℝ) ≤ stT240 242 := by
  have hc : ((-4223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108585999/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-4223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c243 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((833557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -365801/2500000) (δ := 6047/500000000) (ψ := -109777/200000) 240 210
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t243 : ((1069389481/20000000000 : ℚ) : ℝ) ≤ stT240 243 := by
  have hc : ((833507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1069389481/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((833507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c244 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((230231/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 250219/2500000) (δ := 6047/500000000) (ψ := -109777/200000) 240 210
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t244 : ((36845550051/625000000000 : ℚ) : ℝ) ≤ stT240 244 := by
  have hc : ((460437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36845550051/625000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((460437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c245 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((187737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1727423/5000000) (δ := 12047/500000000) (ψ := -109777/200000) 240 210
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t245 : ((29977179953/2500000000000 : ℚ) : ℝ) ≤ stT240 245 := by
  have hc : ((187687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29977179953/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((187687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c246 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-70947/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 737357/1250000) (δ := 6047/500000000) (ψ := -109777/200000) 240 210
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t246 : ((-5654670413/125000000000 : ℚ) : ℝ) ≤ stT240 246 := by
  have hc : ((-8869/12500 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5654670413/125000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-8869/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c247 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-122713/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7375027/10000000) (δ := 751/62500000) (ψ := -109777/200000) 240 211
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t247 : ((-62467534389/1000000000000 : ℚ) : ℝ) ≤ stT240 247 := by
  have hc : ((-490877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62467534389/1000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-490877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c248 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-49771/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4950787/10000000) (δ := 751/62500000) (ψ := -109777/200000) 240 211
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t248 : ((-126434414109/5000000000000 : ℚ) : ℝ) ≤ stT240 248 := by
  have hc : ((-199109/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126434414109/5000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-199109/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c249 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((264009/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2536327/10000000) (δ := 751/62500000) (ψ := -109777/200000) 240 211
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t249 : ((2613953069/78125000000 : ℚ) : ℝ) ≤ stT240 249 := by
  have hc : ((16499/31250 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2613953069/78125000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((16499/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c250 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((499309/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -131467/10000000) (δ := 751/62500000) (ψ := -109777/200000) 240 211
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t250 : ((15788733111/250000000000 : ℚ) : ℝ) ≤ stT240 250 := by
  have hc : ((124821/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15788733111/250000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((124821/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c251 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((308649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2263733/10000000) (δ := 751/62500000) (ψ := -109777/200000) 240 211
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t251 : ((6087550533/156250000000 : ℚ) : ℝ) ≤ stT240 251 := by
  have hc : ((19289/31250 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6087550533/156250000000 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((19289/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c252 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-71239/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4649393/10000000) (δ := 751/62500000) (ψ := -109777/200000) 240 211
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t252 : ((-89768482323/5000000000000 : ℚ) : ℝ) ≤ stT240 252 := by
  have hc : ((-142503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).2
  have h0 : (0:ℝ) ≤ ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89768482323/5000000000000 : ℚ) : ℝ)
      = ((629941/10000000 : ℚ) : ℝ) * ((-142503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c253 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-945607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7025633/10000000) (δ := 751/62500000) (ψ := -109777/200000) 240 211
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t253 : ((-118905965523/2000000000000 : ℚ) : ℝ) ≤ stT240 253 := by
  have hc : ((-945657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118905965523/2000000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-945657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c254 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-163307/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -126309/200000) (δ := 3031/250000000) (ψ := -109777/200000) 240 212
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t254 : ((-400289967/7812500000 : ℚ) : ℝ) ≤ stT240 254 := by
  have hc : ((-163317/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-400289967/7812500000 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-163317/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c255 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-12351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -395787/1000000) (δ := 3031/250000000) (ψ := -109777/200000) 240 212
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t255 : ((-310632649/400000000000 : ℚ) : ℝ) ≤ stT240 255 := by
  have hc : ((-12401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-310632649/400000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-12401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c256 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((799813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -160953/1000000) (δ := 3031/250000000) (ψ := -109777/200000) 240 212
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t256 : ((799763/16000000 : ℚ) : ℝ) ≤ stT240 256 := by
  have hc : ((799763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).1
  have hw2 : ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((799763/16000000 : ℚ) : ℝ)
      = ((1/16 : ℚ) : ℝ) * ((799763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c257 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((957713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72963/1000000) (δ := 3031/250000000) (ψ := -109777/200000) 240 212
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t257 : ((298686470733/5000000000000 : ℚ) : ℝ) ≤ stT240 257 := by
  have hc : ((957663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298686470733/5000000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((957663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c258 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((84997/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 305973/1000000) (δ := 3031/250000000) (ψ := -109777/200000) 240 212
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t258 : ((26454485067/1250000000000 : ℚ) : ℝ) ≤ stT240 258 := by
  have hc : ((169969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26454485067/1250000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((169969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c259 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-137327/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 538083/1000000) (δ := 3031/250000000) (ψ := -109777/200000) 240 212
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t259 : ((-17067729023/500000000000 : ℚ) : ℝ) ≤ stT240 259 := by
  have hc : ((-274679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).2
  have h0 : (0:ℝ) ≤ ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17067729023/500000000000 : ℚ) : ℝ)
      = ((62137/1000000 : ℚ) : ℝ) * ((-274679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c260 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-997927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 769299/1000000) (δ := 3031/250000000) (ψ := -109777/200000) 240 212
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t260 : ((-309459693999/5000000000000 : ℚ) : ℝ) ≤ stT240 260 := by
  have hc : ((-997977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-309459693999/5000000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-997977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c261 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-163693/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2855847/5000000) (δ := 3043/250000000) (ψ := -109777/200000) 240 213
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t261 : ((-40532499567/1000000000000 : ℚ) : ℝ) ≤ stT240 261 := by
  have hc : ((-327411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40532499567/1000000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-327411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c262 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((202493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1708617/5000000) (δ := 9043/250000000) (ψ := -109777/200000) 240 213
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t262 : ((62534845143/5000000000000 : ℚ) : ℝ) ≤ stT240 262 := by
  have hc : ((202443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).1
  have hw2 : ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62534845143/5000000000000 : ℚ) : ℝ)
      = ((308901/5000000 : ℚ) : ℝ) * ((202443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c263 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((899307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -565767/5000000) (δ := 3043/250000000) (ψ := -109777/200000) 240 213
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t263 : ((277252623441/5000000000000 : ℚ) : ℝ) ≤ stT240 263 := by
  have hc : ((899257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((277252623441/5000000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((899257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c264 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((448423/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 572763/5000000) (δ := 9043/250000000) (ψ := -109777/200000) 240 213
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t264 : ((137984843943/2500000000000 : ℚ) : ℝ) ≤ stT240 264 := by
  have hc : ((224199/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137984843943/2500000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((224199/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c265 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((203781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1706973/5000000) (δ := 3043/250000000) (ψ := -109777/200000) 240 213
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t265 : ((25030186929/2000000000000 : ℚ) : ℝ) ≤ stT240 265 := by
  have hc : ((203731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25030186929/2000000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((203731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c266 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-128651/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2836923/5000000) (δ := 3043/250000000) (ψ := -109777/200000) 240 213
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t266 : ((-3944360277/100000000000 : ℚ) : ℝ) ≤ stT240 266 := by
  have hc : ((-128661/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3944360277/100000000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-128661/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c267 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-499797/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7782737/10000000) (δ := 2413/200000000) (ψ := -109777/200000) 240 214
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t267 : ((-152943282801/2500000000000 : ℚ) : ℝ) ≤ stT240 267 := by
  have hc : ((-249911/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152943282801/2500000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-249911/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c268 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-150321/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5539757/10000000) (δ := 2413/200000000) (ψ := -109777/200000) 240 214
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t268 : ((-5739432363/156250000000 : ℚ) : ℝ) ≤ stT240 268 := by
  have hc : ((-300667/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5739432363/156250000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-300667/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c269 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((15387/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3305117/10000000) (δ := 2413/200000000) (ψ := -109777/200000) 240 214
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t269 : ((7503761941/500000000000 : ℚ) : ℝ) ≤ stT240 269 := by
  have hc : ((123071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7503761941/500000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((123071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c270 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((454169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1078757/10000000) (δ := 2413/200000000) (ψ := -109777/200000) 240 214
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t270 : ((26990523/488281250 : ℚ) : ℝ) ≤ stT240 270 := by
  have hc : ((14192/15625 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26990523/488281250 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((14192/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c271 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((89793/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1139383/10000000) (δ := 2413/200000000) (ψ := -109777/200000) 240 214
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t271 : ((426111401/7812500000 : ℚ) : ℝ) ≤ stT240 271 := by
  have hc : ((22447/25000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((426111401/7812500000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((22447/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c272 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((7157/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3349303/10000000) (δ := 2413/200000000) (ψ := -109777/200000) 240 214
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t272 : ((69417933093/5000000000000 : ℚ) : ℝ) ≤ stT240 272 := by
  have hc : ((114487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).1
  have hw2 : ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69417933093/5000000000000 : ℚ) : ℝ)
      = ((606339/10000000 : ℚ) : ℝ) * ((114487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c273 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-60491/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5551123/10000000) (δ := 2413/200000000) (ψ := -109777/200000) 240 214
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t273 : ((-572091767/15625000000 : ℚ) : ℝ) ≤ stT240 273 := by
  have hc : ((-3781/6250 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-572091767/15625000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-3781/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c274 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-999049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7744963/10000000) (δ := 2413/200000000) (ψ := -109777/200000) 240 214
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t274 : ((-603578685177/10000000000000 : ℚ) : ℝ) ≤ stT240 274 := by
  have hc : ((-999099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-603578685177/10000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-999099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c275 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-674367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -288863/500000) (δ := 2409/200000000) (ψ := -109777/200000) 240 215
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t275 : ((-406688962591/10000000000000 : ℚ) : ℝ) ≤ stT240 275 := by
  have hc : ((-674417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-406688962591/10000000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-674417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c276 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((13067/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -179969/500000) (δ := 2409/200000000) (ψ := -109777/200000) 240 215
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t276 : ((3931198299/500000000000 : ℚ) : ℝ) ≤ stT240 276 := by
  have hc : ((6531/50000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3931198299/500000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((6531/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c277 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((840959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17867/125000) (δ := 2409/200000000) (ψ := -109777/200000) 240 215
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t277 : ((505252604469/10000000000000 : ℚ) : ℝ) ≤ stT240 277 := by
  have hc : ((840909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((505252604469/10000000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((840909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c278 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((957347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 229/3125) (δ := 2409/200000000) (ψ := -109777/200000) 240 215
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t278 : ((7176855609/125000000000 : ℚ) : ℝ) ≤ stT240 278 := by
  have hc : ((957297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7176855609/125000000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((957297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c279 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((404043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72179/250000) (δ := 2409/200000000) (ψ := -109777/200000) 240 215
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t279 : ((60466036303/2500000000000 : ℚ) : ℝ) ≤ stT240 279 := by
  have hc : ((403993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).1
  have hw2 : ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149671/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60466036303/2500000000000 : ℚ) : ℝ)
      = ((149671/2500000 : ℚ) : ℝ) * ((403993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c280 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-214219/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50339/100000) (δ := 2409/200000000) (ψ := -109777/200000) 240 215
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t280 : ((-6401771403/250000000000 : ℚ) : ℝ) ≤ stT240 280 := by
  have hc : ((-53561/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6401771403/250000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-53561/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c281 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-963119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71729/100000) (δ := 2409/200000000) (ψ := -109777/200000) 240 215
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t281 : ((-11491569339/200000000000 : ℚ) : ℝ) ≤ stT240 281 := by
  have hc : ((-963169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11491569339/200000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-963169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c282 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-26137/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6403623/10000000) (δ := 1519/125000000) (ψ := -109777/200000) 240 216
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t282 : ((-62261219441/1250000000000 : ℚ) : ℝ) ≤ stT240 282 := by
  have hc : ((-418217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).2
  have h0 : (0:ℝ) ≤ ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62261219441/1250000000000 : ℚ) : ℝ)
      = ((148873/2500000 : ℚ) : ℝ) * ((-418217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c283 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-140633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4279743/10000000) (δ := 1519/125000000) (ψ := -109777/200000) 240 216
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t283 : ((-83627461837/10000000000000 : ℚ) : ℝ) ≤ stT240 283 := by
  have hc : ((-140683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).2
  have h0 : (0:ℝ) ≤ ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83627461837/10000000000000 : ℚ) : ℝ)
      = ((594439/10000000 : ℚ) : ℝ) * ((-140683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c284 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((162099/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2163303/10000000) (δ := 1519/125000000) (ψ := -109777/200000) 240 216
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t284 : ((19236101647/500000000000 : ℚ) : ℝ) ≤ stT240 284 := by
  have hc : ((324173/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19236101647/500000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((324173/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c285 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((249941/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54363/10000000) (δ := 1519/125000000) (ψ := -109777/200000) 240 216
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t285 : ((74022323559/1250000000000 : ℚ) : ℝ) ≤ stT240 285 := by
  have hc : ((499857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).1
  have hw2 : ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((148087/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74022323559/1250000000000 : ℚ) : ℝ)
      = ((148087/2500000 : ℚ) : ℝ) * ((499857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c286 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((683023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2047257/10000000) (δ := 1519/125000000) (ψ := -109777/200000) 240 216
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t286 : ((25240633161/625000000000 : ℚ) : ℝ) ≤ stT240 286 := by
  have hc : ((682973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).1
  have hw2 : ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((36957/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25240633161/625000000000 : ℚ) : ℝ)
      = ((36957/625000 : ℚ) : ℝ) * ((682973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c287 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-85697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4141497/10000000) (δ := 1519/125000000) (ψ := -109777/200000) 240 216
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t287 : ((-25307455327/5000000000000 : ℚ) : ℝ) ≤ stT240 287 := by
  have hc : ((-85747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25307455327/5000000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-85747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c288 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-795947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6228417/10000000) (δ := 1519/125000000) (ψ := -109777/200000) 240 216
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t288 : ((-58630751029/1250000000000 : ℚ) : ℝ) ≤ stT240 288 := by
  have hc : ((-795997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).2
  have h0 : (0:ℝ) ≤ ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58630751029/1250000000000 : ℚ) : ℝ)
      = ((73657/1250000 : ℚ) : ℝ) * ((-795997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c289 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-196709/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7399827/10000000) (δ := 759/62500000) (ψ := -109777/200000) 240 217
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t289 : ((-28929299421/500000000000 : ℚ) : ℝ) ≤ stT240 289 := by
  have hc : ((-196719/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).2
  have h0 : (0:ℝ) ≤ ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28929299421/500000000000 : ℚ) : ℝ)
      = ((147059/2500000 : ℚ) : ℝ) * ((-196719/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c290 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-531273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5327247/10000000) (δ := 759/62500000) (ψ := -109777/200000) 240 217
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t290 : ((-312004023383/10000000000000 : ℚ) : ℝ) ≤ stT240 290 := by
  have hc : ((-531323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).2
  have h0 : (0:ℝ) ≤ ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-312004023383/10000000000000 : ℚ) : ℝ)
      = ((587221/10000000 : ℚ) : ℝ) * ((-531323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c291 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((131461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3261867/10000000) (δ := 759/62500000) (ψ := -109777/200000) 240 217
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t291 : ((1926227439/125000000000 : ℚ) : ℝ) ≤ stT240 291 := by
  have hc : ((32859/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1926227439/125000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((32859/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c292 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((443173/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1203507/10000000) (δ := 759/62500000) (ψ := -109777/200000) 240 217
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t292 : ((12966621267/250000000000 : ℚ) : ℝ) ≤ stT240 292 := by
  have hc : ((110787/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).1
  have hw2 : ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117041/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12966621267/250000000000 : ℚ) : ℝ)
      = ((117041/2000000 : ℚ) : ℝ) * ((110787/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c293 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((943051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 847773/10000000) (δ := 759/62500000) (ψ := -109777/200000) 240 217
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t293 : ((275453421103/5000000000000 : ℚ) : ℝ) ≤ stT240 293 := by
  have hc : ((943001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).1
  have hw2 : ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((292103/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((275453421103/5000000000000 : ℚ) : ℝ)
      = ((292103/5000000 : ℚ) : ℝ) * ((943001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c294 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((402259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2892033/10000000) (δ := 759/62500000) (ψ := -109777/200000) 240 217
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t294 : ((234572713099/10000000000000 : ℚ) : ℝ) ≤ stT240 294 := by
  have hc : ((402209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).1
  have hw2 : ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((583211/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234572713099/10000000000000 : ℚ) : ℝ)
      = ((583211/10000000 : ℚ) : ℝ) * ((402209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c295 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-390303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4929393/10000000) (δ := 759/62500000) (ψ := -109777/200000) 240 217
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t295 : ((-227272494719/10000000000000 : ℚ) : ℝ) ≤ stT240 295 := by
  have hc : ((-390353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).2
  have h0 : (0:ℝ) ≤ ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-227272494719/10000000000000 : ℚ) : ℝ)
      = ((582223/10000000 : ℚ) : ℝ) * ((-390353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c296 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-468361/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6959853/10000000) (δ := 759/62500000) (ψ := -109777/200000) 240 217
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t296 : ((-136122105127/2500000000000 : ℚ) : ℝ) ≤ stT240 296 := by
  have hc : ((-234193/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).2
  have h0 : (0:ℝ) ≤ ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136122105127/2500000000000 : ℚ) : ℝ)
      = ((581239/10000000 : ℚ) : ℝ) * ((-234193/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c297 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-56229/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -672449/1000000) (δ := 3009/250000000) (ψ := -109777/200000) 240 218
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t297 : ((-261033572963/5000000000000 : ℚ) : ℝ) ≤ stT240 297 := by
  have hc : ((-449857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).2
  have h0 : (0:ℝ) ≤ ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-261033572963/5000000000000 : ℚ) : ℝ)
      = ((580259/10000000 : ℚ) : ℝ) * ((-449857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c298 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-76809/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -470771/1000000) (δ := 3009/250000000) (ψ := -109777/200000) 240 218
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t298 : ((-17800617051/1000000000000 : ℚ) : ℝ) ≤ stT240 298 := by
  have hc : ((-153643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).2
  have h0 : (0:ℝ) ≤ ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17800617051/1000000000000 : ℚ) : ℝ)
      = ((115857/2000000 : ℚ) : ℝ) * ((-153643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c299 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((472157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53953/200000) (δ := 3009/250000000) (ψ := -109777/200000) 240 218
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t299 : ((136513043799/5000000000000 : ℚ) : ℝ) ≤ stT240 299 := by
  have hc : ((472107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).1
  have hw2 : ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((289157/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136513043799/5000000000000 : ℚ) : ℝ)
      = ((289157/5000000 : ℚ) : ℝ) * ((472107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c300 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((480841/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -69431/1000000) (δ := 3009/250000000) (ψ := -109777/200000) 240 218
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t300 : ((346998897/6250000000 : ℚ) : ℝ) ≤ stT240 300 := by
  have hc : ((30051/31250 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((346998897/6250000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((30051/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c301 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((216837/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 130237/1000000) (δ := 3009/250000000) (ψ := -109777/200000) 240 218
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t301 : ((24995094711/500000000000 : ℚ) : ℝ) ≤ stT240 301 := by
  have hc : ((433649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).1
  have hw2 : ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57639/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24995094711/500000000000 : ℚ) : ℝ)
      = ((57639/1000000 : ℚ) : ℝ) * ((433649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c302 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((2511/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 65849/200000) (δ := 3009/250000000) (ψ := -109777/200000) 240 218
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t302 : ((577851827/40000000000 : ℚ) : ℝ) ≤ stT240 302 := by
  have hc : ((5021/20000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).1
  have hw2 : ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((115087/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((577851827/40000000000 : ℚ) : ℝ)
      = ((115087/2000000 : ℚ) : ℝ) * ((5021/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c303 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-128443/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 527593/1000000) (δ := 3009/250000000) (ψ := -109777/200000) 240 218
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t303 : ((-29518303167/1000000000000 : ℚ) : ℝ) ≤ stT240 303 := by
  have hc : ((-256911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29518303167/1000000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-256911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c304 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-30351/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 725287/1000000) (δ := 3009/250000000) (ψ := -109777/200000) 240 218
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t304 : ((-13926726957/250000000000 : ℚ) : ℝ) ≤ stT240 304 := by
  have hc : ((-485641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13926726957/250000000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-485641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c305 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-213429/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6484693/10000000) (δ := 6037/500000000) (ψ := -109777/200000) 240 219
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t305 : ((-244432778917/5000000000000 : ℚ) : ℝ) ≤ stT240 305 := by
  have hc : ((-426883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).2
  have h0 : (0:ℝ) ≤ ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244432778917/5000000000000 : ℚ) : ℝ)
      = ((572599/10000000 : ℚ) : ℝ) * ((-426883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c306 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-235239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4520653/10000000) (δ := 6037/500000000) (ψ := -109777/200000) 240 219
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t306 : ((-67252890159/5000000000000 : ℚ) : ℝ) ≤ stT240 306 := by
  have hc : ((-235289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).2
  have h0 : (0:ℝ) ≤ ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67252890159/5000000000000 : ℚ) : ℝ)
      = ((285831/5000000 : ℚ) : ℝ) * ((-235289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c307 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((32431/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2563093/10000000) (δ := 6037/500000000) (ψ := -109777/200000) 240 219
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t307 : ((14806048879/500000000000 : ℚ) : ℝ) ≤ stT240 307 := by
  have hc : ((259423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14806048879/500000000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((259423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c308 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((242549/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -611893/10000000) (δ := 6037/500000000) (ψ := -109777/200000) 240 219
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t308 : ((138197782773/2500000000000 : ℚ) : ℝ) ≤ stT240 308 := by
  have hc : ((485073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138197782773/2500000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((485073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c309 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((13456/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1333007/10000000) (δ := 6037/500000000) (ψ := -109777/200000) 240 219
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t309 : ((3061761937/62500000000 : ℚ) : ℝ) ≤ stT240 309 := by
  have hc : ((430567/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3061761937/62500000000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((430567/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c310 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((259161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3271607/10000000) (δ := 6037/500000000) (ψ := -109777/200000) 240 219
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t310 : ((147164942671/10000000000000 : ℚ) : ℝ) ≤ stT240 310 := by
  have hc : ((259111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).1
  have hw2 : ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567961/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147164942671/10000000000000 : ℚ) : ℝ)
      = ((567961/10000000 : ℚ) : ℝ) * ((259111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c311 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-61111/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5204027/10000000) (δ := 6037/500000000) (ψ := -109777/200000) 240 219
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t311 : ((-17328207189/625000000000 : ℚ) : ℝ) ≤ stT240 311 := by
  have hc : ((-244469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17328207189/625000000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-244469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c312 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-958377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7130147/10000000) (δ := 6037/500000000) (ψ := -109777/200000) 240 219
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t312 : ((-542602903353/10000000000000 : ℚ) : ℝ) ≤ stT240 312 := by
  have hc : ((-958427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-542602903353/10000000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-958427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c313 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-443851/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -832227/1250000) (δ := 12181/1000000000) (ψ := -109777/200000) 240 220
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t313 : ((-31361725873/625000000000 : ℚ) : ℝ) ≤ stT240 313 := by
  have hc : ((-110969/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31361725873/625000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-110969/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c314 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-320993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37062/78125) (δ := 12181/1000000000) (ψ := -109777/200000) 240 220
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t314 : ((-181175159319/10000000000000 : ℚ) : ℝ) ≤ stT240 314 := by
  have hc : ((-321043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).2
  have h0 : (0:ℝ) ≤ ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181175159319/10000000000000 : ℚ) : ℝ)
      = ((564333/10000000 : ℚ) : ℝ) * ((-321043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c315 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((211317/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -709029/2500000) (δ := 12181/1000000000) (ψ := -109777/200000) 240 220
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t315 : ((7440594957/312500000000 : ℚ) : ℝ) ≤ stT240 315 := by
  have hc : ((52823/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7440594957/312500000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((52823/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c316 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((116371/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -233589/2500000) (δ := 12181/1000000000) (ψ := -109777/200000) 240 220
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t316 : ((261840702237/5000000000000 : ℚ) : ℝ) ≤ stT240 316 := by
  have hc : ((465459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261840702237/5000000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((465459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c317 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((231743/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15021/156250) (δ := 12181/1000000000) (ψ := -109777/200000) 240 220
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t317 : ((52061037591/1000000000000 : ℚ) : ℝ) ≤ stT240 317 := by
  have hc : ((463461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).1
  have hw2 : ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((112331/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52061037591/1000000000000 : ℚ) : ℝ)
      = ((112331/2000000 : ℚ) : ℝ) * ((463461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c318 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((417193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 89097/312500) (δ := 12181/1000000000) (ψ := -109777/200000) 240 220
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t318 : ((58480528599/2500000000000 : ℚ) : ℝ) ≤ stT240 318 := by
  have hc : ((417143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).1
  have hw2 : ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140193/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58480528599/2500000000000 : ℚ) : ℝ)
      = ((140193/2500000 : ℚ) : ℝ) * ((417143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c319 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-397/1250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 591873/1250000) (δ := 12181/1000000000) (ψ := -109777/200000) 240 220
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t319 : ((-3557000229/200000000000 : ℚ) : ℝ) ≤ stT240 319 := by
  have hc : ((-6353/20000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3557000229/200000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-6353/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c320 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-10991/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51663/78125) (δ := 12181/1000000000) (ψ := -109777/200000) 240 220
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t320 : ((-49156041861/1000000000000 : ℚ) : ℝ) ≤ stT240 320 := by
  have hc : ((-87933/100000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49156041861/1000000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-87933/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c321 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-242079/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -361149/500000) (δ := 2423/200000000) (ψ := -109777/200000) 240 221
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t321 : ((-135122402359/2500000000000 : ℚ) : ℝ) ≤ stT240 321 := by
  have hc : ((-484183/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135122402359/2500000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-484183/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c322 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-54123/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -267837/500000) (δ := 2423/200000000) (ψ := -109777/200000) 240 221
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t322 : ((-1885274857/62500000000 : ℚ) : ℝ) ≤ stT240 322 := by
  have hc : ((-3383/6250 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).2
  have h0 : (0:ℝ) ≤ ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1885274857/62500000000 : ℚ) : ℝ)
      = ((557279/10000000 : ℚ) : ℝ) * ((-3383/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c323 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((171441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -174813/500000) (δ := 2423/200000000) (ψ := -109777/200000) 240 221
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t323 : ((47682175937/5000000000000 : ℚ) : ℝ) ≤ stT240 323 := by
  have hc : ((171391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).1
  have hw2 : ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278207/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47682175937/5000000000000 : ℚ) : ℝ)
      = ((278207/5000000 : ℚ) : ℝ) * ((171391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c324 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((396031/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -82077/500000) (δ := 2423/200000000) (ψ := -109777/200000) 240 221
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t324 : ((22000311333/500000000000 : ℚ) : ℝ) ≤ stT240 324 := by
  have hc : ((198003/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22000311333/500000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((198003/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c325 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((12457/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10371/500000) (δ := 2423/200000000) (ψ := -109777/200000) 240 221
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t325 : ((552764097/10000000000 : ℚ) : ℝ) ≤ stT240 325 := by
  have hc : ((99651/100000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((552764097/10000000000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((99651/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c326 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((136401/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102537/500000) (δ := 2423/200000000) (ψ := -109777/200000) 240 221
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t326 : ((9442485321/250000000000 : ℚ) : ℝ) ≤ stT240 326 := by
  have hc : ((136391/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).1
  have hw2 : ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69231/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9442485321/250000000000 : ℚ) : ℝ)
      = ((69231/1250000 : ℚ) : ℝ) * ((136391/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c327 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((3857/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 194421/500000) (δ := 2423/200000000) (ψ := -109777/200000) 240 221
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t327 : ((4252024689/5000000000000 : ℚ) : ℝ) ≤ stT240 327 := by
  have hc : ((7689/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).1
  have hw2 : ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((553001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4252024689/5000000000000 : ℚ) : ℝ)
      = ((553001/10000000 : ℚ) : ℝ) * ((7689/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c328 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-657437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143013/250000) (δ := 2423/200000000) (ψ := -109777/200000) 240 221
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t328 : ((-181518353473/5000000000000 : ℚ) : ℝ) ≤ stT240 328 := by
  have hc : ((-657487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181518353473/5000000000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-657487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c329 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-992469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 377349/500000) (δ := 2423/200000000) (ψ := -109777/200000) 240 221
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t329 : ((-273596795021/5000000000000 : ℚ) : ℝ) ≤ stT240 329 := by
  have hc : ((-992519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).2
  have h0 : (0:ℝ) ≤ ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-273596795021/5000000000000 : ℚ) : ℝ)
      = ((275659/5000000 : ℚ) : ℝ) * ((-992519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c330 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-32887/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6340043/10000000) (δ := 1501/125000000) (ψ := -109777/200000) 240 222
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t330 : ((-9052401249/200000000000 : ℚ) : ℝ) ≤ stT240 330 := by
  have hc : ((-32889/40000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).2
  have h0 : (0:ℝ) ≤ ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9052401249/200000000000 : ℚ) : ℝ)
      = ((275241/5000000 : ℚ) : ℝ) * ((-32889/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c331 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-236783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4524623/10000000) (δ := 1501/125000000) (ψ := -109777/200000) 240 222
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t331 : ((-2603505169/200000000000 : ℚ) : ℝ) ≤ stT240 331 := by
  have hc : ((-236833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2603505169/200000000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-236833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c332 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((466147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2714663/10000000) (δ := 1501/125000000) (ψ := -109777/200000) 240 222
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t332 : ((255803821637/10000000000000 : ℚ) : ℝ) ≤ stT240 332 := by
  have hc : ((466097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).1
  have hw2 : ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((255803821637/10000000000000 : ℚ) : ℝ)
      = ((548821/10000000 : ℚ) : ℝ) * ((466097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c333 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((934457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -910163/10000000) (δ := 1501/125000000) (ψ := -109777/200000) 240 222
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t333 : ((128012824593/2500000000000 : ℚ) : ℝ) ≤ stT240 333 := by
  have hc : ((934407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128012824593/2500000000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((934407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c334 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((937447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 888937/10000000) (δ := 1501/125000000) (ψ := -109777/200000) 240 222
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t334 : ((20516808139/400000000000 : ℚ) : ℝ) ≤ stT240 334 := by
  have hc : ((937397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20516808139/400000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((937397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c335 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((477421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2682697/10000000) (δ := 1501/125000000) (ψ := -109777/200000) 240 222
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t335 : ((130407732409/5000000000000 : ℚ) : ℝ) ≤ stT240 335 := by
  have hc : ((477371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130407732409/5000000000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((477371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c336 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-215913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4471057/10000000) (δ := 1501/125000000) (ψ := -109777/200000) 240 222
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t336 : ((-23563506967/2000000000000 : ℚ) : ℝ) ≤ stT240 336 := by
  have hc : ((-215963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).2
  have h0 : (0:ℝ) ≤ ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23563506967/2000000000000 : ℚ) : ℝ)
      = ((109109/2000000 : ℚ) : ℝ) * ((-215963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c337 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-802133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6254137/10000000) (δ := 1501/125000000) (ψ := -109777/200000) 240 222
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t337 : ((-87395431301/2000000000000 : ℚ) : ℝ) ≤ stT240 337 := by
  have hc : ((-802183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).2
  have h0 : (0:ℝ) ≤ ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87395431301/2000000000000 : ℚ) : ℝ)
      = ((108947/2000000 : ℚ) : ℝ) * ((-802183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c338 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-997469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3838043/5000000) (δ := 12103/1000000000) (ψ := -109777/200000) 240 223
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t338 : ((-542579512151/10000000000000 : ℚ) : ℝ) ≤ stT240 338 := by
  have hc : ((-997519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).2
  have h0 : (0:ℝ) ≤ ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-542579512151/10000000000000 : ℚ) : ℝ)
      = ((543929/10000000 : ℚ) : ℝ) * ((-997519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c339 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-35539/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2951753/5000000) (δ := 12103/1000000000) (ψ := -109777/200000) 240 223
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t339 : ((-19303512729/500000000000 : ℚ) : ℝ) ≤ stT240 339 := by
  have hc : ((-71083/100000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19303512729/500000000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-71083/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c340 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-20897/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2068103/5000000) (δ := 12103/1000000000) (ψ := -109777/200000) 240 223
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t340 : ((-22679572813/5000000000000 : ℚ) : ℝ) ≤ stT240 340 := by
  have hc : ((-41819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).2
  have h0 : (0:ℝ) ≤ ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22679572813/5000000000000 : ℚ) : ℝ)
      = ((542327/10000000 : ℚ) : ℝ) * ((-41819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c341 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((581967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1187063/5000000) (δ := 12103/1000000000) (ψ := -109777/200000) 240 223
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t341 : ((31512551301/1000000000000 : ℚ) : ℝ) ≤ stT240 341 := by
  have hc : ((581917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).1
  have hw2 : ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((54153/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31512551301/1000000000000 : ℚ) : ℝ)
      = ((54153/1000000 : ℚ) : ℝ) * ((581917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c342 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((193937/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -308573/5000000) (δ := 12103/1000000000) (ψ := -109777/200000) 240 223
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t342 : ((52431849063/1000000000000 : ℚ) : ℝ) ≤ stT240 342 := by
  have hc : ((193927/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).1
  have hw2 : ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((270369/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52431849063/1000000000000 : ℚ) : ℝ)
      = ((270369/5000000 : ℚ) : ℝ) * ((193927/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c343 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((898757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 567337/5000000) (δ := 12103/1000000000) (ψ := -109777/200000) 240 223
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t343 : ((485255945943/10000000000000 : ℚ) : ℝ) ≤ stT240 343 := by
  have hc : ((898707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((485255945943/10000000000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((898707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c344 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((50769/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1440697/5000000) (δ := 12103/1000000000) (ψ := -109777/200000) 240 223
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t344 : ((109477586313/5000000000000 : ℚ) : ℝ) ≤ stT240 344 := by
  have hc : ((203051/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).1
  have hw2 : ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539163/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109477586313/5000000000000 : ℚ) : ℝ)
      = ((539163/10000000 : ℚ) : ℝ) * ((203051/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c345 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-5497/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2311537/5000000) (δ := 12103/1000000000) (ψ := -109777/200000) 240 223
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t345 : ((-740006059/50000000000 : ℚ) : ℝ) ≤ stT240 345 := by
  have hc : ((-2749/10000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).2
  have h0 : (0:ℝ) ≤ ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-740006059/50000000000 : ℚ) : ℝ)
      = ((269191/5000000 : ℚ) : ℝ) * ((-2749/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c346 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-165323/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3179827/5000000) (δ := 12103/1000000000) (ψ := -109777/200000) 240 223
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t346 : ((-22220920533/500000000000 : ℚ) : ℝ) ≤ stT240 346 := by
  have hc : ((-165333/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).2
  have h0 : (0:ℝ) ≤ ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22220920533/500000000000 : ℚ) : ℝ)
      = ((134401/2500000 : ℚ) : ℝ) * ((-165333/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c347 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-1991/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -761671/1000000) (δ := 12193/1000000000) (ψ := -109777/200000) 240 224
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t347 : ((-10688802219/200000000000 : ℚ) : ℝ) ≤ stT240 347 := by
  have hc : ((-19911/20000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).2
  have h0 : (0:ℝ) ≤ ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10688802219/200000000000 : ℚ) : ℝ)
      = ((536829/10000000 : ℚ) : ℝ) * ((-19911/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c348 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-141399/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -589009/1000000) (δ := 12193/1000000000) (ψ := -109777/200000) 240 224
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t348 : ((-75803284313/2000000000000 : ℚ) : ℝ) ≤ stT240 348 := by
  have hc : ((-141409/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).2
  have h0 : (0:ℝ) ≤ ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75803284313/2000000000000 : ℚ) : ℝ)
      = ((536057/10000000 : ℚ) : ℝ) * ((-141409/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c349 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-9641/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -416839/1000000) (δ := 12193/1000000000) (ψ := -109777/200000) 240 224
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t349 : ((-322711753/62500000000 : ℚ) : ℝ) ≤ stT240 349 := by
  have hc : ((-4823/50000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).2
  have h0 : (0:ℝ) ≤ ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-322711753/62500000000 : ℚ) : ℝ)
      = ((66911/1250000 : ℚ) : ℝ) * ((-4823/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c350 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((139117/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -245167/1000000) (δ := 12193/1000000000) (ψ := -109777/200000) 240 224
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t350 : ((74354415549/2500000000000 : ℚ) : ℝ) ≤ stT240 350 := by
  have hc : ((278209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).1
  have hw2 : ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((267261/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74354415549/2500000000000 : ℚ) : ℝ)
      = ((267261/5000000 : ℚ) : ℝ) * ((278209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c351 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((956533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -73981/1000000) (δ := 12193/1000000000) (ψ := -109777/200000) 240 224
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t351 : ((398853411/7812500000 : ℚ) : ℝ) ≤ stT240 351 := by
  have hc : ((956483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).1
  have hw2 : ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((834/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((398853411/7812500000 : ℚ) : ℝ)
      = ((834/15625 : ℚ) : ℝ) * ((956483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c352 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((926101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 96713/1000000) (δ := 12193/1000000000) (ψ := -109777/200000) 240 224
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t352 : ((493586109051/10000000000000 : ℚ) : ℝ) ≤ stT240 352 := by
  have hc : ((926051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).1
  have hw2 : ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((533001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((493586109051/10000000000000 : ℚ) : ℝ)
      = ((533001/10000000 : ℚ) : ℝ) * ((926051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c353 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((241067/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 266927/1000000) (δ := 12193/1000000000) (ψ := -109777/200000) 240 224
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t353 : ((32073410083/1250000000000 : ℚ) : ℝ) ≤ stT240 353 := by
  have hc : ((120521/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).1
  have hw2 : ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((266123/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32073410083/1250000000000 : ℚ) : ℝ)
      = ((266123/5000000 : ℚ) : ℝ) * ((120521/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c354 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-174943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 436661/1000000) (δ := 12193/1000000000) (ψ := -109777/200000) 240 224
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t354 : ((-18601580907/2000000000000 : ℚ) : ℝ) ≤ stT240 354 := by
  have hc : ((-174993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).2
  have h0 : (0:ℝ) ≤ ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18601580907/2000000000000 : ℚ) : ℝ)
      = ((106299/2000000 : ℚ) : ℝ) * ((-174993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c355 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-11768/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 605909/1000000) (δ := 12193/1000000000) (ψ := -109777/200000) 240 224
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t355 : ((-39975819549/1000000000000 : ℚ) : ℝ) ≤ stT240 355 := by
  have hc : ((-376601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39975819549/1000000000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-376601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c356 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-999083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 774689/1000000) (δ := 12193/1000000000) (ψ := -109777/200000) 240 224
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t356 : ((-529539490867/10000000000000 : ℚ) : ℝ) ≤ stT240 356 := by
  have hc : ((-999133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).2
  have h0 : (0:ℝ) ≤ ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-529539490867/10000000000000 : ℚ) : ℝ)
      = ((529999/10000000 : ℚ) : ℝ) * ((-999133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c357 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-807813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6278073/10000000) (δ := 6043/500000000) (ψ := -109777/200000) 240 225
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t357 : ((-427567147791/10000000000000 : ℚ) : ℝ) ≤ stT240 357 := by
  have hc : ((-807863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).2
  have h0 : (0:ℝ) ≤ ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-427567147791/10000000000000 : ℚ) : ℝ)
      = ((529257/10000000 : ℚ) : ℝ) * ((-807863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c358 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-265869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4599753/10000000) (δ := 6043/500000000) (ψ := -109777/200000) 240 225
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t358 : ((-140542712123/10000000000000 : ℚ) : ℝ) ≤ stT240 358 := by
  have hc : ((-265919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).2
  have h0 : (0:ℝ) ≤ ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140542712123/10000000000000 : ℚ) : ℝ)
      = ((528517/10000000 : ℚ) : ℝ) * ((-265919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c359 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((194871/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2926113/10000000) (δ := 6043/500000000) (ψ := -109777/200000) 240 225
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t359 : ((51417813517/2500000000000 : ℚ) : ℝ) ≤ stT240 359 := by
  have hc : ((97423/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51417813517/2500000000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((97423/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c360 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((876219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1257093/10000000) (δ := 6043/500000000) (ψ := -109777/200000) 240 225
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t360 : ((230890683387/5000000000000 : ℚ) : ℝ) ≤ stT240 360 := by
  have hc : ((876169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).1
  have hw2 : ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230890683387/5000000000000 : ℚ) : ℝ)
      = ((263523/5000000 : ℚ) : ℝ) * ((876169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c361 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((986761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 407247/10000000) (δ := 6043/500000000) (ψ := -109777/200000) 240 225
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t361 : ((103864159993/2000000000000 : ℚ) : ℝ) ≤ stT240 361 := by
  have hc : ((986711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103864159993/2000000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((986711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c362 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((338613/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2067027/10000000) (δ := 6043/500000000) (ψ := -109777/200000) 240 225
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t362 : ((11122361859/312500000000 : ℚ) : ℝ) ≤ stT240 362 := by
  have hc : ((84647/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11122361859/312500000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((84647/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c363 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((8183/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3722187/10000000) (δ := 6043/500000000) (ψ := -109777/200000) 240 225
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t363 : ((2146164807/500000000000 : ℚ) : ℝ) ≤ stT240 363 := by
  have hc : ((4089/50000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).1
  have hw2 : ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((524863/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2146164807/500000000000 : ℚ) : ℝ)
      = ((524863/10000000 : ℚ) : ℝ) * ((4089/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c364 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-546617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5372787/10000000) (δ := 6043/500000000) (ψ := -109777/200000) 240 225
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t364 : ((-286531681381/10000000000000 : ℚ) : ℝ) ≤ stT240 364 := by
  have hc : ((-546667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286531681381/10000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-546667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c365 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-472363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7018887/10000000) (δ := 6043/500000000) (ψ := -109777/200000) 240 225
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t365 : ((-1931712629/39062500000 : ℚ) : ℝ) ≤ stT240 365 := by
  have hc : ((-118097/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1931712629/39062500000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-118097/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c366 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-474207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1761869/2500000) (δ := 1503/125000000) (ψ := -109777/200000) 240 226
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t366 : ((-30985666811/625000000000 : ℚ) : ℝ) ≤ stT240 366 := by
  have hc : ((-59279/62500 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30985666811/625000000000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-59279/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c367 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-111829/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -676297/1250000) (δ := 1503/125000000) (ψ := -109777/200000) 240 226
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t367 : ((-14594877661/500000000000 : ℚ) : ℝ) ≤ stT240 367 := by
  have hc : ((-111839/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14594877661/500000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-111839/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c368 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((29837/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -944429/2500000) (δ := 1503/125000000) (ψ := -109777/200000) 240 226
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t368 : ((1942572279/625000000000 : ℚ) : ℝ) ≤ stT240 368 := by
  have hc : ((7453/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1942572279/625000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((7453/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c369 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((65259/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -268687/1250000) (δ := 1503/125000000) (ψ := -109777/200000) 240 226
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t369 : ((16984931033/500000000000 : ℚ) : ℝ) ≤ stT240 369 := by
  have hc : ((32627/50000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16984931033/500000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((32627/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c370 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((122247/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65707/1250000) (δ := 1503/125000000) (ψ := -109777/200000) 240 226
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t370 : ((2033597117/40000000000 : ℚ) : ℝ) ≤ stT240 370 := by
  have hc : ((488963/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).1
  have hw2 : ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((4159/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2033597117/40000000000 : ℚ) : ℝ)
      = ((4159/80000 : ℚ) : ℝ) * ((488963/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c371 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((181163/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 68359/625000) (δ := 1503/125000000) (ψ := -109777/200000) 240 226
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t371 : ((47024963811/1000000000000 : ℚ) : ℝ) ≤ stT240 371 := by
  have hc : ((181153/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).1
  have hw2 : ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((259587/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47024963811/1000000000000 : ℚ) : ℝ)
      = ((259587/5000000 : ℚ) : ℝ) * ((181153/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c372 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((117053/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 338603/1250000) (δ := 1503/125000000) (ψ := -109777/200000) 240 226
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t372 : ((4854605859/200000000000 : ℚ) : ℝ) ≤ stT240 372 := by
  have hc : ((234081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).1
  have hw2 : ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((20739/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4854605859/200000000000 : ℚ) : ℝ)
      = ((20739/400000 : ℚ) : ℝ) * ((234081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c373 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-156393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 134987/312500) (δ := 1503/125000000) (ψ := -109777/200000) 240 226
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t373 : ((-81003212983/10000000000000 : ℚ) : ℝ) ≤ stT240 373 := by
  have hc : ((-156443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).2
  have h0 : (0:ℝ) ≤ ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81003212983/10000000000000 : ℚ) : ℝ)
      = ((517781/10000000 : ℚ) : ℝ) * ((-156443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c374 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-71707/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1481491/2500000) (δ := 1503/125000000) (ψ := -109777/200000) 240 226
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t374 : ((-36212319/976562500 : ℚ) : ℝ) ≤ stT240 374 := by
  have hc : ((-2241/3125 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36212319/976562500 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-2241/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c375 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-495759/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 470509/625000) (δ := 1503/125000000) (ψ := -109777/200000) 240 226
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t375 : ((-16001366627/312500000000 : ℚ) : ℝ) ≤ stT240 375 := by
  have hc : ((-61973/62500 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).2
  have h0 : (0:ℝ) ≤ ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16001366627/312500000000 : ℚ) : ℝ)
      = ((258199/5000000 : ℚ) : ℝ) * ((-61973/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c376 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-34933/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6581959/10000000) (δ := 12131/1000000000) (ψ := -109777/200000) 240 227
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t376 : ((-3603272757/80000000000 : ℚ) : ℝ) ≤ stT240 376 := by
  have hc : ((-6987/8000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).2
  have h0 : (0:ℝ) ≤ ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3603272757/80000000000 : ℚ) : ℝ)
      = ((515711/10000000 : ℚ) : ℝ) * ((-6987/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c377 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-102977/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4988359/10000000) (δ := 12131/1000000000) (ψ := -109777/200000) 240 227
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t377 : ((-106084746433/5000000000000 : ℚ) : ℝ) ≤ stT240 377 := by
  have hc : ((-205979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).2
  have h0 : (0:ℝ) ≤ ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106084746433/5000000000000 : ℚ) : ℝ)
      = ((515027/10000000 : ℚ) : ℝ) * ((-205979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c378 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((104823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3398959/10000000) (δ := 12131/1000000000) (ψ := -109777/200000) 240 227
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t378 : ((3368888907/312500000000 : ℚ) : ℝ) ≤ stT240 378 := by
  have hc : ((52399/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3368888907/312500000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((52399/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c379 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((748181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1813699/10000000) (δ := 12131/1000000000) (ψ := -109777/200000) 240 227
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t379 : ((76857742023/2000000000000 : ℚ) : ℝ) ≤ stT240 379 := by
  have hc : ((748131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).1
  have hw2 : ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102733/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76857742023/2000000000000 : ℚ) : ℝ)
      = ((102733/2000000 : ℚ) : ℝ) * ((748131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c380 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((995671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -232699/10000000) (δ := 12131/1000000000) (ψ := -109777/200000) 240 227
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t380 : ((510742621169/10000000000000 : ℚ) : ℝ) ≤ stT240 380 := by
  have hc : ((995621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).1
  have hw2 : ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((510742621169/10000000000000 : ℚ) : ℝ)
      = ((512989/10000000 : ℚ) : ℝ) * ((995621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c381 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((858907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1344161/10000000) (δ := 12131/1000000000) (ψ := -109777/200000) 240 227
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t381 : ((88001064791/2000000000000 : ℚ) : ℝ) ≤ stT240 381 := by
  have hc : ((858857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).1
  have hw2 : ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102463/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88001064791/2000000000000 : ℚ) : ℝ)
      = ((102463/2000000 : ℚ) : ℝ) * ((858857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c382 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((196559/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2916941/10000000) (δ := 12131/1000000000) (ψ := -109777/200000) 240 227
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t382 : ((12569430237/625000000000 : ℚ) : ℝ) ≤ stT240 382 := by
  have hc : ((98267/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12569430237/625000000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((98267/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c383 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-110779/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4485521/10000000) (δ := 12131/1000000000) (ψ := -109777/200000) 240 227
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t383 : ((-14154573877/1250000000000 : ℚ) : ℝ) ≤ stT240 383 := by
  have hc : ((-27701/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).2
  have h0 : (0:ℝ) ≤ ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14154573877/1250000000000 : ℚ) : ℝ)
      = ((510977/10000000 : ℚ) : ℝ) * ((-27701/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c384 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-93847/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6050081/10000000) (δ := 12131/1000000000) (ψ := -109777/200000) 240 227
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t384 : ((-191577383443/5000000000000 : ℚ) : ℝ) ≤ stT240 384 := by
  have hc : ((-375413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).2
  have h0 : (0:ℝ) ≤ ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191577383443/5000000000000 : ℚ) : ℝ)
      = ((510311/10000000 : ℚ) : ℝ) * ((-375413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c385 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-995263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7610561/10000000) (δ := 12131/1000000000) (ψ := -109777/200000) 240 227
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t385 : ((-31703704989/625000000000 : ℚ) : ℝ) ≤ stT240 385 := by
  have hc : ((-995313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).2
  have h0 : (0:ℝ) ≤ ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31703704989/625000000000 : ℚ) : ℝ)
      = ((31853/625000 : ℚ) : ℝ) * ((-995313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c386 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-216307/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6541003/10000000) (δ := 2433/200000000) (ψ := -109777/200000) 240 228
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t386 : ((-220207626693/5000000000000 : ℚ) : ℝ) ≤ stT240 386 := by
  have hc : ((-432639/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220207626693/5000000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-432639/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c387 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-82401/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4988623/10000000) (δ := 2433/200000000) (ψ := -109777/200000) 240 228
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t387 : ((-41891901219/2000000000000 : ℚ) : ℝ) ≤ stT240 387 := by
  have hc : ((-82411/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41891901219/2000000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-82411/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c388 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((193487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3440203/10000000) (δ := 2433/200000000) (ψ := -109777/200000) 240 228
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t388 : ((98202742101/10000000000000 : ℚ) : ℝ) ≤ stT240 388 := by
  have hc : ((193437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).1
  have hw2 : ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98202742101/10000000000000 : ℚ) : ℝ)
      = ((507673/10000000 : ℚ) : ℝ) * ((193437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c389 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((90749/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1895803/10000000) (δ := 2433/200000000) (ψ := -109777/200000) 240 228
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t389 : ((9201677821/250000000000 : ℚ) : ℝ) ≤ stT240 389 := by
  have hc : ((362971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).1
  have hw2 : ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25351/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9201677821/250000000000 : ℚ) : ℝ)
      = ((25351/500000 : ℚ) : ℝ) * ((362971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c390 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((494957/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -355363/10000000) (δ := 2433/200000000) (ψ := -109777/200000) 240 228
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t390 : ((62654555477/1250000000000 : ℚ) : ℝ) ≤ stT240 390 := by
  have hc : ((123733/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).1
  have hw2 : ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((506369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62654555477/1250000000000 : ℚ) : ℝ)
      = ((506369/10000000 : ℚ) : ℝ) * ((123733/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c391 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((890457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1181117/10000000) (δ := 2433/200000000) (ψ := -109777/200000) 240 228
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t391 : ((450297518447/10000000000000 : ℚ) : ℝ) ≤ stT240 391 := by
  have hc : ((890407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((450297518447/10000000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((890407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c392 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((466489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2713697/10000000) (δ := 2433/200000000) (ψ := -109777/200000) 240 228
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t392 : ((58896786091/2500000000000 : ℚ) : ℝ) ≤ stT240 392 := by
  have hc : ((466439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58896786091/2500000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((466439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c393 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-6291/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4242377/10000000) (δ := 2433/200000000) (ψ := -109777/200000) 240 228
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t393 : ((-3174655379/500000000000 : ℚ) : ℝ) ≤ stT240 393 := by
  have hc : ((-12587/100000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).2
  have h0 : (0:ℝ) ≤ ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3174655379/500000000000 : ℚ) : ℝ)
      = ((252217/5000000 : ℚ) : ℝ) * ((-12587/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c394 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-335689/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5767157/10000000) (δ := 2433/200000000) (ψ := -109777/200000) 240 228
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t394 : ((-84565181601/2500000000000 : ℚ) : ℝ) ≤ stT240 394 := by
  have hc : ((-167857/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).2
  have h0 : (0:ℝ) ≤ ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84565181601/2500000000000 : ℚ) : ℝ)
      = ((503793/10000000 : ℚ) : ℝ) * ((-167857/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c395 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-487243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7288037/10000000) (δ := 2433/200000000) (ψ := -109777/200000) 240 228
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t395 : ((-12258566527/250000000000 : ℚ) : ℝ) ≤ stT240 395 := by
  have hc : ((-121817/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12258566527/250000000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-121817/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c396 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-928493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3451413/5000000) (δ := 12057/1000000000) (ψ := -109777/200000) 240 229
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t396 : ((-466610499817/10000000000000 : ℚ) : ℝ) ≤ stT240 396 := by
  have hc : ((-928543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).2
  have h0 : (0:ℝ) ≤ ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-466610499817/10000000000000 : ℚ) : ℝ)
      = ((502519/10000000 : ℚ) : ℝ) * ((-928543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c397 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-138061/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2694813/5000000) (δ := 12057/1000000000) (ψ := -109777/200000) 240 229
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t397 : ((-69297156621/2500000000000 : ℚ) : ℝ) ≤ stT240 397 := by
  have hc : ((-276147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69297156621/2500000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-276147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c398 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((18737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1940073/5000000) (δ := 12057/1000000000) (ψ := -109777/200000) 240 229
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t398 : ((4683466749/5000000000000 : ℚ) : ℝ) ≤ stT240 398 := by
  have hc : ((18687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).1
  have hw2 : ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250627/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4683466749/5000000000000 : ℚ) : ℝ)
      = ((250627/5000000 : ℚ) : ℝ) * ((18687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c399 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((145461/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1187253/5000000) (δ := 12057/1000000000) (ψ := -109777/200000) 240 229
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t399 : ((72815300761/2500000000000 : ℚ) : ℝ) ≤ stT240 399 := by
  have hc : ((290897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).1
  have hw2 : ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72815300761/2500000000000 : ℚ) : ℝ)
      = ((250313/5000000 : ℚ) : ℝ) * ((290897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c400 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((187939/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -436323/5000000) (δ := 12057/1000000000) (ψ := -109777/200000) 240 229
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t400 : ((187929/4000000 : ℚ) : ℝ) ≤ stT240 400 := by
  have hc : ((187929/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).1
  have hw2 : ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/20 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187929/4000000 : ℚ) : ℝ)
      = ((1/20 : ℚ) : ℝ) * ((187929/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c401 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((30277/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 312747/5000000) (δ := 12057/1000000000) (ψ := -109777/200000) 240 229
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t401 : ((15118826877/312500000000 : ℚ) : ℝ) ≤ stT240 401 := by
  have hc : ((484407/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).1
  have hw2 : ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31211/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15118826877/312500000000 : ℚ) : ℝ)
      = ((31211/625000 : ℚ) : ℝ) * ((484407/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c402 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((82691/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1059927/5000000) (δ := 12057/1000000000) (ψ := -109777/200000) 240 229
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t402 : ((82478699603/2500000000000 : ℚ) : ℝ) ≤ stT240 402 := by
  have hc : ((330739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).1
  have hw2 : ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((249377/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82478699603/2500000000000 : ℚ) : ℝ)
      = ((249377/5000000 : ℚ) : ℝ) * ((330739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c403 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((126237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1805277/5000000) (δ := 12057/1000000000) (ψ := -109777/200000) 240 229
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t403 : ((12571632249/2000000000000 : ℚ) : ℝ) ≤ stT240 403 := by
  have hc : ((126187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).1
  have hw2 : ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((99627/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12571632249/2000000000000 : ℚ) : ℝ)
      = ((99627/2000000 : ℚ) : ℝ) * ((126187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c404 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-14103/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2548767/5000000) (δ := 12057/1000000000) (ψ := -109777/200000) 240 229
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t404 : ((-112276605287/5000000000000 : ℚ) : ℝ) ≤ stT240 404 := by
  have hc : ((-225673/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).2
  have h0 : (0:ℝ) ≤ ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112276605287/5000000000000 : ℚ) : ℝ)
      = ((497519/10000000 : ℚ) : ℝ) * ((-225673/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c405 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-87311/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3290427/5000000) (δ := 12057/1000000000) (ψ := -109777/200000) 240 229
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t405 : ((-1355864677/31250000000 : ℚ) : ℝ) ≤ stT240 405 := by
  have hc : ((-21829/25000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).2
  have h0 : (0:ℝ) ≤ ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1355864677/31250000000 : ℚ) : ℝ)
      = ((62113/1250000 : ℚ) : ℝ) * ((-21829/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c406 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-996589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7647449/10000000) (δ := 12053/1000000000) (ψ := -109777/200000) 240 230
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t406 : ((-123655990647/2500000000000 : ℚ) : ℝ) ≤ stT240 406 := by
  have hc : ((-996639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).2
  have h0 : (0:ℝ) ≤ ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123655990647/2500000000000 : ℚ) : ℝ)
      = ((124073/2500000 : ℚ) : ℝ) * ((-996639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c407 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-781947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6171449/10000000) (δ := 12053/1000000000) (ψ := -109777/200000) 240 230
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t407 : ((-193810918477/5000000000000 : ℚ) : ℝ) ≤ stT240 407 := by
  have hc : ((-781997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).2
  have h0 : (0:ℝ) ≤ ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193810918477/5000000000000 : ℚ) : ℝ)
      = ((247841/5000000 : ℚ) : ℝ) * ((-781997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c408 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-151969/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4699049/10000000) (δ := 12053/1000000000) (ψ := -109777/200000) 240 230
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t408 : ((-18812069389/1250000000000 : ℚ) : ℝ) ≤ stT240 408 := by
  have hc : ((-75997/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).2
  have h0 : (0:ℝ) ≤ ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18812069389/1250000000000 : ℚ) : ℝ)
      = ((247537/5000000 : ℚ) : ℝ) * ((-75997/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c409 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((275103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3230249/10000000) (δ := 12053/1000000000) (ψ := -109777/200000) 240 230
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t409 : ((34001226701/2500000000000 : ℚ) : ℝ) ≤ stT240 409 := by
  have hc : ((275053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34001226701/2500000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((275053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c410 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((15219/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1765049/10000000) (δ := 12053/1000000000) (ψ := -109777/200000) 240 230
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t410 : ((469726397/12500000000 : ℚ) : ℝ) ≤ stT240 410 := by
  have hc : ((7609/10000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).1
  have hw2 : ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61733/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((469726397/12500000000 : ℚ) : ℝ)
      = ((61733/1250000 : ℚ) : ℝ) * ((7609/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c411 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((198529/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -303389/10000000) (δ := 12053/1000000000) (ψ := -109777/200000) 240 230
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t411 : ((97922077497/2000000000000 : ℚ) : ℝ) ≤ stT240 411 := by
  have hc : ((198519/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).1
  have hw2 : ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((493263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97922077497/2000000000000 : ℚ) : ℝ)
      = ((493263/10000000 : ℚ) : ℝ) * ((198519/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c412 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((895221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1154671/10000000) (δ := 12053/1000000000) (ψ := -109777/200000) 240 230
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t412 : ((55127315693/1250000000000 : ℚ) : ℝ) ≤ stT240 412 := by
  have hc : ((895171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).1
  have hw2 : ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61583/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55127315693/1250000000000 : ℚ) : ℝ)
      = ((61583/1250000 : ℚ) : ℝ) * ((895171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c413 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((251523/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2609191/10000000) (δ := 12053/1000000000) (ψ := -109777/200000) 240 230
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t413 : ((61876933183/2500000000000 : ℚ) : ℝ) ≤ stT240 413 := by
  have hc : ((125749/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).1
  have hw2 : ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((492067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61876933183/2500000000000 : ℚ) : ℝ)
      = ((492067/10000000 : ℚ) : ℝ) * ((125749/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c414 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-53271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4060231/10000000) (δ := 12053/1000000000) (ψ := -109777/200000) 240 230
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t414 : ((-13102942577/5000000000000 : ℚ) : ℝ) ≤ stT240 414 := by
  have hc : ((-53321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13102942577/5000000000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-53321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c415 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-295509/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5507791/10000000) (δ := 12053/1000000000) (ψ := -109777/200000) 240 230
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t415 : ((-72536012727/2500000000000 : ℚ) : ℝ) ≤ stT240 415 := by
  have hc : ((-147767/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72536012727/2500000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-147767/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c416 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-935591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6951811/10000000) (δ := 12053/1000000000) (ψ := -109777/200000) 240 230
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t416 : ((-458736361531/10000000000000 : ℚ) : ℝ) ≤ stT240 416 := by
  have hc : ((-935641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-458736361531/10000000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-935641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c417 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-976897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -228611/312500) (δ := 19/1562500) (ψ := -109777/200000) 240 231
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t417 : ((-478413876741/10000000000000 : ℚ) : ℝ) ≤ stT240 417 := by
  have hc : ((-976947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-478413876741/10000000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-976947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c418 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-703689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -183701/312500) (δ := 19/1562500) (ψ := -109777/200000) 240 231
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t418 : ((-86052501181/2500000000000 : ℚ) : ℝ) ≤ stT240 418 := by
  have hc : ((-703739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).2
  have h0 : (0:ℝ) ≤ ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86052501181/2500000000000 : ℚ) : ℝ)
      = ((122279/2500000 : ℚ) : ℝ) * ((-703739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c419 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-205619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1111183/2500000) (δ := 19/1562500) (ψ := -109777/200000) 240 231
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t419 : ((-25118971977/2500000000000 : ℚ) : ℝ) ≤ stT240 419 := by
  have hc : ((-205669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).2
  have h0 : (0:ℝ) ≤ ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25118971977/2500000000000 : ℚ) : ℝ)
      = ((122133/2500000 : ℚ) : ℝ) * ((-205669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c420 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((89241/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -753613/2500000) (δ := 19/1562500) (ψ := -109777/200000) 240 231
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t420 : ((1741561863/100000000000 : ℚ) : ℝ) ≤ stT240 420 := by
  have hc : ((178457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1741561863/100000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((178457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c421 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((16101/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -198449/1250000) (δ := 19/1562500) (ψ := -109777/200000) 240 231
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t421 : ((7846657/200000000 : ℚ) : ℝ) ≤ stT240 421 := by
  have hc : ((161/200 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7846657/200000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((161/200 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c422 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((997847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41023/2500000) (δ := 19/1562500) (ψ := -109777/200000) 240 231
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t422 : ((60714949653/1250000000000 : ℚ) : ℝ) ≤ stT240 422 := by
  have hc : ((997797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60714949653/1250000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((997797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c423 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((54777/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 313997/2500000) (δ := 19/1562500) (ψ := -109777/200000) 240 231
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t423 : ((26631934407/625000000000 : ℚ) : ℝ) ≤ stT240 423 := by
  have hc : ((438191/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26631934407/625000000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((438191/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c424 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((480907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 20881/78125) (δ := 19/1562500) (ψ := -109777/200000) 240 231
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t424 : ((116762177597/5000000000000 : ℚ) : ℝ) ≤ stT240 424 := by
  have hc : ((480857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).1
  have hw2 : ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((242821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116762177597/5000000000000 : ℚ) : ℝ)
      = ((242821/5000000 : ℚ) : ℝ) * ((480857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c425 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-15909/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1021547/2500000) (δ := 19/1562500) (ψ := -109777/200000) 240 231
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t425 : ((-965384231/312500000000 : ℚ) : ℝ) ≤ stT240 425 := by
  have hc : ((-31843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-965384231/312500000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-31843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c426 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-293653/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1374077/2500000) (δ := 19/1562500) (ψ := -109777/200000) 240 231
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t426 : ((-35571894589/1250000000000 : ℚ) : ℝ) ≤ stT240 426 := by
  have hc : ((-146839/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35571894589/1250000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-146839/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c427 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-464269/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 862891/1250000) (δ := 19/1562500) (ψ := -109777/200000) 240 231
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t427 : ((-56171913149/1250000000000 : ℚ) : ℝ) ≤ stT240 427 := by
  have hc : ((-232147/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56171913149/1250000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-232147/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c428 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-983657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -231293/312500) (δ := 1517/125000000) (ψ := -109777/200000) 240 232
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t428 : ((-475493468883/10000000000000 : ℚ) : ℝ) ≤ stT240 428 := by
  have hc : ((-983707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-475493468883/10000000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-983707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c429 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-73769/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -750137/1250000) (δ := 1517/125000000) (ψ := -109777/200000) 240 232
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t429 : ((-3561845607/100000000000 : ℚ) : ℝ) ≤ stT240 429 := by
  have hc : ((-36887/50000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3561845607/100000000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-36887/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c430 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-267551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1151029/2500000) (δ := 1517/125000000) (ψ := -109777/200000) 240 232
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t430 : ((-129048709043/10000000000000 : ℚ) : ℝ) ≤ stT240 430 := by
  have hc : ((-267601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129048709043/10000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-267601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c431 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((141357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -802609/2500000) (δ := 1517/125000000) (ψ := -109777/200000) 240 232
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t431 : ((17019305439/1250000000000 : ℚ) : ℝ) ≤ stT240 431 := by
  have hc : ((35333/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17019305439/1250000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((35333/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c432 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((186631/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56873/312500) (δ := 1517/125000000) (ψ := -109777/200000) 240 232
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t432 : ((1436589213/40000000000 : ℚ) : ℝ) ≤ stT240 432 := by
  have hc : ((373237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1436589213/40000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((373237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c433 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((197013/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54077/1250000) (δ := 1517/125000000) (ψ := -109777/200000) 240 232
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t433 : ((94673534707/2000000000000 : ℚ) : ℝ) ≤ stT240 433 := by
  have hc : ((197003/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94673534707/2000000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((197003/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c434 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((928447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 118933/1250000) (δ := 1517/125000000) (ψ := -109777/200000) 240 232
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t434 : ((89128897191/2000000000000 : ℚ) : ℝ) ≤ stT240 434 := by
  have hc : ((928397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89128897191/2000000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((928397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c435 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((59547/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 583091/2500000) (δ := 1517/125000000) (ψ := -109777/200000) 240 232
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t435 : ((14274092973/500000000000 : ℚ) : ℝ) ≤ stT240 435 := by
  have hc : ((29771/50000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14274092973/500000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((29771/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c436 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((43327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 927521/2500000) (δ := 1517/125000000) (ψ := -109777/200000) 240 232
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t436 : ((10368945363/2500000000000 : ℚ) : ℝ) ≤ stT240 436 := by
  have hc : ((21651/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10368945363/2500000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((21651/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c437 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-223341/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 317789/625000) (δ := 1517/125000000) (ψ := -109777/200000) 240 232
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t437 : ((-10685047659/500000000000 : ℚ) : ℝ) ≤ stT240 437 := by
  have hc : ((-111683/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).2
  have h0 : (0:ℝ) ≤ ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10685047659/500000000000 : ℚ) : ℝ)
      = ((95673/2000000 : ℚ) : ℝ) * ((-111683/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c438 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-423853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 807013/1250000) (δ := 1517/125000000) (ψ := -109777/200000) 240 232
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t438 : ((-101268481041/2500000000000 : ℚ) : ℝ) ≤ stT240 438 := by
  have hc : ((-211939/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101268481041/2500000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-211939/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c439 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-99993/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1956101/2500000) (δ := 1517/125000000) (ψ := -109777/200000) 240 232
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t439 : ((-11931611363/250000000000 : ℚ) : ℝ) ≤ stT240 439 := by
  have hc : ((-49999/50000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11931611363/250000000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-49999/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c440 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-172131/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6518379/10000000) (δ := 12029/1000000000) (ψ := -109777/200000) 240 233
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t440 : ((-20516280803/500000000000 : ℚ) : ℝ) ≤ stT240 440 := by
  have hc : ((-172141/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20516280803/500000000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-172141/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c441 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-472153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5156319/10000000) (δ := 12029/1000000000) (ψ := -109777/200000) 240 233
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t441 : ((-224858818773/10000000000000 : ℚ) : ℝ) ≤ stT240 441 := by
  have hc : ((-472203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224858818773/10000000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-472203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c442 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((10369/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3797319/10000000) (δ := 12029/1000000000) (ψ := -109777/200000) 240 233
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t442 : ((4927268709/2000000000000 : ℚ) : ℝ) ≤ stT240 442 := by
  have hc : ((10359/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).1
  have hw2 : ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((475651/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4927268709/2000000000000 : ℚ) : ℝ)
      = ((475651/10000000 : ℚ) : ℝ) * ((10359/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c443 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((559883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2441379/10000000) (δ := 12029/1000000000) (ψ := -109777/200000) 240 233
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t443 : ((132992247981/5000000000000 : ℚ) : ℝ) ≤ stT240 443 := by
  have hc : ((559833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).1
  have hw2 : ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237557/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132992247981/5000000000000 : ℚ) : ℝ)
      = ((237557/5000000 : ℚ) : ℝ) * ((559833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c444 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((453351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1088499/10000000) (δ := 12029/1000000000) (ψ := -109777/200000) 240 233
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t444 : ((53784636607/1250000000000 : ℚ) : ℝ) ≤ stT240 444 := by
  have hc : ((226663/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).1
  have hw2 : ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237289/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53784636607/1250000000000 : ℚ) : ℝ)
      = ((237289/5000000 : ℚ) : ℝ) * ((226663/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c445 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((497271/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 261321/10000000) (δ := 12029/1000000000) (ψ := -109777/200000) 240 233
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t445 : ((23571698007/500000000000 : ℚ) : ℝ) ≤ stT240 445 := by
  have hc : ((248623/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).1
  have hw2 : ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94809/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23571698007/500000000000 : ℚ) : ℝ)
      = ((94809/2000000 : ℚ) : ℝ) * ((248623/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c446 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((800147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1608141/10000000) (δ := 12029/1000000000) (ψ := -109777/200000) 240 233
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t446 : ((378856330761/10000000000000 : ℚ) : ℝ) ≤ stT240 446 := by
  have hc : ((800097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((378856330761/10000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((800097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c447 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((190111/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2951901/10000000) (δ := 12029/1000000000) (ψ := -109777/200000) 240 233
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t447 : ((44953723269/2500000000000 : ℚ) : ℝ) ≤ stT240 447 := by
  have hc : ((95043/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44953723269/2500000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((95043/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c448 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-145771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4292721/10000000) (δ := 12029/1000000000) (ψ := -109777/200000) 240 233
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t448 : ((-8611750797/1250000000000 : ℚ) : ℝ) ≤ stT240 448 := by
  have hc : ((-145821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).2
  have h0 : (0:ℝ) ≤ ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8611750797/1250000000000 : ℚ) : ℝ)
      = ((59057/1250000 : ℚ) : ℝ) * ((-145821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c449 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-314939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5630481/10000000) (δ := 12029/1000000000) (ψ := -109777/200000) 240 233
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t449 : ((-3716024013/125000000000 : ℚ) : ℝ) ≤ stT240 449 := by
  have hc : ((-78741/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).2
  have h0 : (0:ℝ) ≤ ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3716024013/125000000000 : ℚ) : ℝ)
      = ((47193/1000000 : ℚ) : ℝ) * ((-78741/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c450 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-468741/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6965301/10000000) (δ := 12029/1000000000) (ψ := -109777/200000) 240 233
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t450 : ((-22097863623/500000000000 : ℚ) : ℝ) ≤ stT240 450 := by
  have hc : ((-234383/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).2
  have h0 : (0:ℝ) ≤ ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22097863623/500000000000 : ℚ) : ℝ)
      = ((94281/2000000 : ℚ) : ℝ) * ((-234383/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c451 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-984327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3705391/5000000) (δ := 6041/500000000) (ψ := -109777/200000) 240 234
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t451 : ((-231762705257/5000000000000 : ℚ) : ℝ) ≤ stT240 451 := by
  have hc : ((-984377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-231762705257/5000000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-984377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c452 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-759123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3040951/5000000) (δ := 6041/500000000) (ψ := -109777/200000) 240 234
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t452 : ((-357085371453/10000000000000 : ℚ) : ℝ) ≤ stT240 452 := by
  have hc : ((-759173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-357085371453/10000000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-759173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c453 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-325523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2377951/5000000) (δ := 6041/500000000) (ψ := -109777/200000) 240 234
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t453 : ((-152967543893/10000000000000 : ℚ) : ℝ) ≤ stT240 453 := by
  have hc : ((-325573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152967543893/10000000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-325573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c454 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((196351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1716451/5000000) (δ := 6041/500000000) (ψ := -109777/200000) 240 234
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t454 : ((92128574223/10000000000000 : ℚ) : ℝ) ≤ stT240 454 := by
  have hc : ((196301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).1
  have hw2 : ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((469323/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92128574223/10000000000000 : ℚ) : ℝ)
      = ((469323/10000000 : ℚ) : ℝ) * ((196301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c455 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((132733/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1056361/5000000) (δ := 6041/500000000) (ψ := -109777/200000) 240 234
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t455 : ((62221471461/2000000000000 : ℚ) : ℝ) ≤ stT240 455 := by
  have hc : ((132723/200000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).1
  have hw2 : ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((468807/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62221471461/2000000000000 : ℚ) : ℝ)
      = ((468807/10000000 : ℚ) : ℝ) * ((132723/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c456 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((474901/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -397741/5000000) (δ := 6041/500000000) (ψ := -109777/200000) 240 234
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t456 : ((13898789487/312500000000 : ℚ) : ℝ) ≤ stT240 456 := by
  have hc : ((118719/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).1
  have hw2 : ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117073/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13898789487/312500000000 : ℚ) : ℝ)
      = ((117073/2500000 : ℚ) : ℝ) * ((118719/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c457 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((978543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 259409/5000000) (δ := 6041/500000000) (ψ := -109777/200000) 240 234
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t457 : ((22885972777/500000000000 : ℚ) : ℝ) ≤ stT240 457 := by
  have hc : ((978493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).1
  have hw2 : ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((23389/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22885972777/500000000000 : ℚ) : ℝ)
      = ((23389/500000 : ℚ) : ℝ) * ((978493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c458 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((743759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 915149/5000000) (δ := 6041/500000000) (ψ := -109777/200000) 240 234
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t458 : ((347512160721/10000000000000 : ℚ) : ℝ) ≤ stT240 458 := by
  have hc : ((743709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).1
  have hw2 : ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((467269/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((347512160721/10000000000000 : ℚ) : ℝ)
      = ((467269/10000000 : ℚ) : ℝ) * ((743709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c459 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((310019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1569479/5000000) (δ := 6041/500000000) (ψ := -109777/200000) 240 234
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t459 : ((3617028261/250000000000 : ℚ) : ℝ) ≤ stT240 459 := by
  have hc : ((309969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).1
  have hw2 : ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11669/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3617028261/250000000000 : ℚ) : ℝ)
      = ((11669/250000 : ℚ) : ℝ) * ((309969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c460 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-102799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2222339/5000000) (δ := 6041/500000000) (ψ := -109777/200000) 240 234
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t460 : ((-5992749809/625000000000 : ℚ) : ℝ) ≤ stT240 460 := by
  have hc : ((-12853/62500 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).2
  have h0 : (0:ℝ) ≤ ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5992749809/625000000000 : ℚ) : ℝ)
      = ((466253/10000000 : ℚ) : ℝ) * ((-12853/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c461 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-665571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2873819/5000000) (δ := 6041/500000000) (ψ := -109777/200000) 240 234
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t461 : ((-310010983887/10000000000000 : ℚ) : ℝ) ≤ stT240 461 := by
  have hc : ((-665621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).2
  have h0 : (0:ℝ) ≤ ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-310010983887/10000000000000 : ℚ) : ℝ)
      = ((465747/10000000 : ℚ) : ℝ) * ((-665621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c462 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-237111/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3523859/5000000) (δ := 6041/500000000) (ψ := -109777/200000) 240 234
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t462 : ((-220640097021/5000000000000 : ℚ) : ℝ) ≤ stT240 462 := by
  have hc : ((-474247/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).2
  have h0 : (0:ℝ) ≤ ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220640097021/5000000000000 : ℚ) : ℝ)
      = ((465243/10000000 : ℚ) : ℝ) * ((-474247/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c463 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-980771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -294517/400000) (δ := 12189/1000000000) (ψ := -109777/200000) 240 235
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t463 : ((-22791337577/500000000000 : ℚ) : ℝ) ≤ stT240 463 := by
  have hc : ((-980821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).2
  have h0 : (0:ℝ) ≤ ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22791337577/500000000000 : ℚ) : ℝ)
      = ((23237/500000 : ℚ) : ℝ) * ((-980821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c464 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-755603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -242737/400000) (δ := 12189/1000000000) (ψ := -109777/200000) 240 235
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t464 : ((-350803593067/10000000000000 : ℚ) : ℝ) ≤ stT240 464 := by
  have hc : ((-755653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).2
  have h0 : (0:ℝ) ≤ ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-350803593067/10000000000000 : ℚ) : ℝ)
      = ((464239/10000000 : ℚ) : ℝ) * ((-755653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c465 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-83343/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -955337/2000000) (δ := 12189/1000000000) (ψ := -109777/200000) 240 235
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t465 : ((-77310392429/5000000000000 : ℚ) : ℝ) ≤ stT240 465 := by
  have hc : ((-166711/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).2
  have h0 : (0:ℝ) ≤ ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77310392429/5000000000000 : ℚ) : ℝ)
      = ((463739/10000000 : ℚ) : ℝ) * ((-166711/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c466 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((43697/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -697553/2000000) (δ := 12189/1000000000) (ψ := -109777/200000) 240 235
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t466 : ((40472902929/5000000000000 : ℚ) : ℝ) ≤ stT240 466 := by
  have hc : ((87369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40472902929/5000000000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((87369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c467 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((39791/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -440321/2000000) (δ := 12189/1000000000) (ψ := -109777/200000) 240 235
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t467 : ((18411600429/625000000000 : ℚ) : ℝ) ≤ stT240 467 := by
  have hc : ((318303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).1
  have hw2 : ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57843/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18411600429/625000000000 : ℚ) : ℝ)
      = ((57843/1250000 : ℚ) : ℝ) * ((318303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c468 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((933307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -183641/2000000) (δ := 12189/1000000000) (ψ := -109777/200000) 240 235
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t468 : ((1725592193/40000000000 : ℚ) : ℝ) ≤ stT240 468 := by
  have hc : ((933257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).1
  have hw2 : ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1725592193/40000000000 : ℚ) : ℝ)
      = ((1849/40000 : ℚ) : ℝ) * ((933257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c469 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((494753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72499/2000000) (δ := 12189/1000000000) (ψ := -109777/200000) 240 235
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t469 : ((28555514637/625000000000 : ℚ) : ℝ) ≤ stT240 469 := by
  have hc : ((61841/62500 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).1
  have hw2 : ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((461757/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28555514637/625000000000 : ℚ) : ℝ)
      = ((461757/10000000 : ℚ) : ℝ) * ((61841/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c470 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((198083/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 328087/2000000) (δ := 12189/1000000000) (ψ := -109777/200000) 240 235
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t470 : ((36545195673/1000000000000 : ℚ) : ℝ) ≤ stT240 470 := by
  have hc : ((396141/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).1
  have hw2 : ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((92253/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36545195673/1000000000000 : ℚ) : ℝ)
      = ((92253/2000000 : ℚ) : ℝ) * ((396141/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c471 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((393583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 116627/400000) (δ := 12189/1000000000) (ψ := -109777/200000) 240 235
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t471 : ((7253206723/400000000000 : ℚ) : ℝ) ≤ stT240 471 := by
  have hc : ((393533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).1
  have hw2 : ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18431/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7253206723/400000000000 : ℚ) : ℝ)
      = ((18431/400000 : ℚ) : ℝ) * ((393533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c472 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-1043/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 837643/2000000) (δ := 12189/1000000000) (ψ := -109777/200000) 240 235
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t472 : ((-1876213/390625000 : ℚ) : ℝ) ≤ stT240 472 := by
  have hc : ((-2087/20000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).2
  have h0 : (0:ℝ) ≤ ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1876213/390625000 : ℚ) : ℝ)
      = ((3596/78125 : ℚ) : ℝ) * ((-2087/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c473 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-287427/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1091611/2000000) (δ := 12189/1000000000) (ψ := -109777/200000) 240 235
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t473 : ((-33042679263/1250000000000 : ℚ) : ℝ) ≤ stT240 473 := by
  have hc : ((-71863/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).2
  have h0 : (0:ℝ) ≤ ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33042679263/1250000000000 : ℚ) : ℝ)
      = ((459801/10000000 : ℚ) : ℝ) * ((-71863/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c474 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-449899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1345051/2000000) (δ := 12189/1000000000) (ψ := -109777/200000) 240 235
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t474 : ((-12916080749/312500000000 : ℚ) : ℝ) ≤ stT240 474 := by
  have hc : ((-112481/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).2
  have h0 : (0:ℝ) ≤ ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12916080749/312500000000 : ℚ) : ℝ)
      = ((114829/2500000 : ℚ) : ℝ) * ((-112481/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c475 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-499263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7718209/10000000) (δ := 12107/1000000000) (ψ := -109777/200000) 240 236
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t475 : ((-1789760247/39062500000 : ℚ) : ℝ) ≤ stT240 475 := by
  have hc : ((-62411/62500 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).2
  have h0 : (0:ℝ) ≤ ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1789760247/39062500000 : ℚ) : ℝ)
      = ((28677/625000 : ℚ) : ℝ) * ((-62411/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c476 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-84777/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6456409/10000000) (δ := 12107/1000000000) (ψ := -109777/200000) 240 236
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t476 : ((-388598297/10000000000 : ℚ) : ℝ) ≤ stT240 476 := by
  have hc : ((-42391/50000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).2
  have h0 : (0:ℝ) ≤ ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-388598297/10000000000 : ℚ) : ℝ)
      = ((9167/200000 : ℚ) : ℝ) * ((-42391/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c477 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-486521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5197249/10000000) (δ := 12107/1000000000) (ψ := -109777/200000) 240 236
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t477 : ((-222785777199/10000000000000 : ℚ) : ℝ) ≤ stT240 477 := by
  have hc : ((-486571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).2
  have h0 : (0:ℝ) ≤ ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222785777199/10000000000000 : ℚ) : ℝ)
      = ((457869/10000000 : ℚ) : ℝ) * ((-486571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c478 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-5471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3940669/10000000) (δ := 12107/1000000000) (ψ := -109777/200000) 240 236
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t478 : ((-252525019/1000000000000 : ℚ) : ℝ) ≤ stT240 478 := by
  have hc : ((-5521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252525019/1000000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-5521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c479 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((237991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2686789/10000000) (δ := 12107/1000000000) (ψ := -109777/200000) 240 236
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t479 : ((54364641513/2500000000000 : ℚ) : ℝ) ≤ stT240 479 := by
  have hc : ((118983/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).1
  have hw2 : ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((456911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54364641513/2500000000000 : ℚ) : ℝ)
      = ((456911/10000000 : ℚ) : ℝ) * ((118983/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c480 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((839643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1435429/10000000) (δ := 12107/1000000000) (ψ := -109777/200000) 240 236
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t480 : ((76643926191/2000000000000 : ℚ) : ℝ) ≤ stT240 480 := by
  have hc : ((839593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).1
  have hw2 : ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76643926191/2000000000000 : ℚ) : ℝ)
      = ((91287/2000000 : ℚ) : ℝ) * ((839593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c481 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((997211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -186769/10000000) (δ := 12107/1000000000) (ψ := -109777/200000) 240 236
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t481 : ((11366638239/250000000000 : ℚ) : ℝ) ≤ stT240 481 := by
  have hc : ((997161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).1
  have hw2 : ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11399/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11366638239/250000000000 : ℚ) : ℝ)
      = ((11399/250000 : ℚ) : ℝ) * ((997161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c482 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((455777/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1059371/10000000) (δ := 12107/1000000000) (ψ := -109777/200000) 240 236
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t482 : ((25948638903/625000000000 : ℚ) : ℝ) ≤ stT240 482 := by
  have hc : ((56969/62500 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).1
  have hw2 : ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((455487/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25948638903/625000000000 : ℚ) : ℝ)
      = ((455487/10000000 : ℚ) : ℝ) * ((56969/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c483 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((302453/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2302871/10000000) (δ := 12107/1000000000) (ψ := -109777/200000) 240 236
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t483 : ((6880463821/250000000000 : ℚ) : ℝ) ≤ stT240 483 := by
  have hc : ((75607/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6880463821/250000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((75607/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c484 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((152657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3543851/10000000) (δ := 12107/1000000000) (ψ := -109777/200000) 240 236
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t484 : ((13873349763/2000000000000 : ℚ) : ℝ) ≤ stT240 484 := by
  have hc : ((152607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13873349763/2000000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((152607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c485 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-335447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4782191/10000000) (δ := 12107/1000000000) (ψ := -109777/200000) 240 236
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t485 : ((-152341471269/10000000000000 : ℚ) : ℝ) ≤ stT240 485 := by
  have hc : ((-335497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).2
  have h0 : (0:ℝ) ≤ ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152341471269/10000000000000 : ℚ) : ℝ)
      = ((454077/10000000 : ℚ) : ℝ) * ((-335497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c486 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-742257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6018071/10000000) (δ := 12107/1000000000) (ψ := -109777/200000) 240 236
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t486 : ((-33671787827/1000000000000 : ℚ) : ℝ) ≤ stT240 486 := by
  have hc : ((-742307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).2
  have h0 : (0:ℝ) ≤ ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33671787827/1000000000000 : ℚ) : ℝ)
      = ((45361/1000000 : ℚ) : ℝ) * ((-742307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c487 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-971089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7251371/10000000) (δ := 12107/1000000000) (ψ := -109777/200000) 240 236
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t487 : ((-55008226377/1250000000000 : ℚ) : ℝ) ≤ stT240 487 := by
  have hc : ((-971139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).2
  have h0 : (0:ℝ) ≤ ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55008226377/1250000000000 : ℚ) : ℝ)
      = ((56643/1250000 : ℚ) : ℝ) * ((-971139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c488 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-484299/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1806453/2500000) (δ := 12003/1000000000) (ψ := -109777/200000) 240 237
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t488 : ((-54810825999/1250000000000 : ℚ) : ℝ) ≤ stT240 488 := by
  have hc : ((-121081/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54810825999/1250000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-121081/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c489 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-184187/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1499403/2500000) (δ := 12003/1000000000) (ψ := -109777/200000) 240 237
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t489 : ((-20824490273/625000000000 : ℚ) : ℝ) ≤ stT240 489 := by
  have hc : ((-368399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20824490273/625000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-368399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c490 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-82889/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -149121/312500) (δ := 12003/1000000000) (ψ := -109777/200000) 240 237
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t490 : ((-37451084231/2500000000000 : ℚ) : ℝ) ≤ stT240 490 := by
  have hc : ((-165803/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37451084231/2500000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-165803/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c491 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((75391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -221787/625000) (δ := 12003/1000000000) (ψ := -109777/200000) 240 237
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t491 : ((17006074119/2500000000000 : ℚ) : ℝ) ≤ stT240 491 := by
  have hc : ((37683/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).1
  have hw2 : ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451293/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17006074119/2500000000000 : ℚ) : ℝ)
      = ((451293/10000000 : ℚ) : ℝ) * ((37683/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c492 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((298463/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -290979/1250000) (δ := 12003/1000000000) (ψ := -109777/200000) 240 237
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t492 : ((33636499323/1250000000000 : ℚ) : ℝ) ≤ stT240 492 := by
  have hc : ((149219/250000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33636499323/1250000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((149219/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c493 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((903111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -138699/1250000) (δ := 12003/1000000000) (ψ := -109777/200000) 240 237
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t493 : ((406717903997/10000000000000 : ℚ) : ℝ) ≤ stT240 493 := by
  have hc : ((903061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((406717903997/10000000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((903061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c494 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((999097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13281/1250000) (δ := 12003/1000000000) (ψ := -109777/200000) 240 237
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t494 : ((449492225287/10000000000000 : ℚ) : ℝ) ≤ stT240 494 := by
  have hc : ((999047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).1
  have hw2 : ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449921/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((449492225287/10000000000000 : ℚ) : ℝ)
      = ((449921/10000000 : ℚ) : ℝ) * ((999047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c495 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((863903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 82473/625000) (δ := 12003/1000000000) (ψ := -109777/200000) 240 237
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t495 : ((194136276249/5000000000000 : ℚ) : ℝ) ≤ stT240 495 := by
  have hc : ((863853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194136276249/5000000000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((863853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c496 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((53/100 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 316311/1250000) (δ := 12003/1000000000) (ψ := -109777/200000) 240 237
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t496 : ((4759088787/200000000000 : ℚ) : ℝ) ≤ stT240 496 := by
  have hc : ((10599/20000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4759088787/200000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((10599/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c497 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((37573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 934737/2500000) (δ := 12003/1000000000) (ψ := -109777/200000) 240 237
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t497 : ((4210642107/1250000000000 : ℚ) : ℝ) ≤ stT240 497 := by
  have hc : ((9387/125000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).1
  have hw2 : ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((448561/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4210642107/1250000000000 : ℚ) : ℝ)
      = ((448561/10000000 : ℚ) : ℝ) * ((9387/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c498 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-49503/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1236237/2500000) (δ := 12003/1000000000) (ψ := -109777/200000) 240 237
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t498 : ((-88742558107/5000000000000 : ℚ) : ℝ) ≤ stT240 498 := by
  have hc : ((-198037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88742558107/5000000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-198037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c499 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-194051/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1537137/2500000) (δ := 12003/1000000000) (ψ := -109777/200000) 240 237
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t499 : ((-86874854537/2500000000000 : ℚ) : ℝ) ≤ stT240 499 := by
  have hc : ((-388127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86874854537/2500000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-388127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_c500 :
    |Real.cos (((240 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((-979729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1837437/2500000) (δ := 12003/1000000000) (ψ := -109777/200000) 240 237
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st240_t500 : ((-219085442853/5000000000000 : ℚ) : ℝ) ≤ stT240 500 := by
  have hc : ((-979779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((240 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st240_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).2
  have h0 : (0:ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219085442853/5000000000000 : ℚ) : ℝ)
      = ((223607/5000000 : ℚ) : ℝ) * ((-979779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st240_p1 : ((853057/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT240 (i+1) := by
  rw [Finset.sum_range_one]
  exact st240_t1

theorem st240_p2 : ((504187913969/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT240 (i+1))
      = (∑ i ∈ Finset.range 1, stT240 (i+1)) + stT240 2 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 1
    simpa using h
  have hprev := st240_p1
  have hstep := st240_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p3 : ((3746577508229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT240 (i+1))
      = (∑ i ∈ Finset.range 2, stT240 (i+1)) + stT240 3 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 2
    simpa using h
  have hprev := st240_p2
  have hstep := st240_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p4 : ((6168295008229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT240 (i+1))
      = (∑ i ∈ Finset.range 3, stT240 (i+1)) + stT240 4 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 3
    simpa using h
  have hprev := st240_p3
  have hstep := st240_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p5 : ((4106973486361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT240 (i+1))
      = (∑ i ∈ Finset.range 4, stT240 (i+1)) + stT240 5 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 4
    simpa using h
  have hprev := st240_p4
  have hstep := st240_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p6 : ((1048042623733/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT240 (i+1))
      = (∑ i ∈ Finset.range 5, stT240 (i+1)) + stT240 6 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 5
    simpa using h
  have hprev := st240_p5
  have hstep := st240_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p7 : ((930847112007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT240 (i+1))
      = (∑ i ∈ Finset.range 6, stT240 (i+1)) + stT240 7 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 6
    simpa using h
  have hprev := st240_p6
  have hstep := st240_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p8 : ((-2586623844787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT240 (i+1))
      = (∑ i ∈ Finset.range 7, stT240 (i+1)) + stT240 8 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 7
    simpa using h
  have hprev := st240_p7
  have hstep := st240_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p9 : ((365722911703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT240 (i+1))
      = (∑ i ∈ Finset.range 8, stT240 (i+1)) + stT240 9 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 8
    simpa using h
  have hprev := st240_p8
  have hstep := st240_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p10 : ((379604641143/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT240 (i+1))
      = (∑ i ∈ Finset.range 9, stT240 (i+1)) + stT240 10 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 9
    simpa using h
  have hprev := st240_p9
  have hstep := st240_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p11 : ((1257857216349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT240 (i+1))
      = (∑ i ∈ Finset.range 10, stT240 (i+1)) + stT240 11 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 10
    simpa using h
  have hprev := st240_p10
  have hstep := st240_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p12 : ((5401498371113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT240 (i+1))
      = (∑ i ∈ Finset.range 11, stT240 (i+1)) + stT240 12 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 11
    simpa using h
  have hprev := st240_p11
  have hstep := st240_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p13 : ((7972283256113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT240 (i+1))
      = (∑ i ∈ Finset.range 12, stT240 (i+1)) + stT240 13 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 12
    simpa using h
  have hprev := st240_p12
  have hstep := st240_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p14 : ((10051866706821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT240 (i+1))
      = (∑ i ∈ Finset.range 13, stT240 (i+1)) + stT240 14 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 13
    simpa using h
  have hprev := st240_p13
  have hstep := st240_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p15 : ((7507523106441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT240 (i+1))
      = (∑ i ∈ Finset.range 14, stT240 (i+1)) + stT240 15 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 14
    simpa using h
  have hprev := st240_p14
  have hstep := st240_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p16 : ((10004583106441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT240 (i+1))
      = (∑ i ∈ Finset.range 15, stT240 (i+1)) + stT240 16 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 15
    simpa using h
  have hprev := st240_p15
  have hstep := st240_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p17 : ((285565551227/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT240 (i+1))
      = (∑ i ∈ Finset.range 16, stT240 (i+1)) + stT240 17 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 16
    simpa using h
  have hprev := st240_p16
  have hstep := st240_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p18 : ((6784376828487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT240 (i+1))
      = (∑ i ∈ Finset.range 17, stT240 (i+1)) + stT240 18 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 17
    simpa using h
  have hprev := st240_p17
  have hstep := st240_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p19 : ((4633860649183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT240 (i+1))
      = (∑ i ∈ Finset.range 18, stT240 (i+1)) + stT240 19 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 18
    simpa using h
  have hprev := st240_p18
  have hstep := st240_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p20 : ((2408832116899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT240 (i+1))
      = (∑ i ∈ Finset.range 19, stT240 (i+1)) + stT240 20 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 19
    simpa using h
  have hprev := st240_p19
  have hstep := st240_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p21 : ((164444427659/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT240 (i+1))
      = (∑ i ∈ Finset.range 20, stT240 (i+1)) + stT240 21 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 20
    simpa using h
  have hprev := st240_p20
  have hstep := st240_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p22 : ((2004006410437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT240 (i+1))
      = (∑ i ∈ Finset.range 21, stT240 (i+1)) + stT240 22 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 21
    simpa using h
  have hprev := st240_p21
  have hstep := st240_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p23 : ((3275846248669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT240 (i+1))
      = (∑ i ∈ Finset.range 22, stT240 (i+1)) + stT240 23 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 22
    simpa using h
  have hprev := st240_p22
  have hstep := st240_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p24 : ((250096205789/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT240 (i+1))
      = (∑ i ∈ Finset.range 23, stT240 (i+1)) + stT240 24 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 23
    simpa using h
  have hprev := st240_p23
  have hstep := st240_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p25 : ((637907405789/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT240 (i+1))
      = (∑ i ∈ Finset.range 24, stT240 (i+1)) + stT240 25 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 24
    simpa using h
  have hprev := st240_p24
  have hstep := st240_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p26 : ((1282403080883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT240 (i+1))
      = (∑ i ∈ Finset.range 25, stT240 (i+1)) + stT240 26 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 25
    simpa using h
  have hprev := st240_p25
  have hstep := st240_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p27 : ((3190161855383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT240 (i+1))
      = (∑ i ∈ Finset.range 26, stT240 (i+1)) + stT240 27 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 26
    simpa using h
  have hprev := st240_p26
  have hstep := st240_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p28 : ((1912093458713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT240 (i+1))
      = (∑ i ∈ Finset.range 27, stT240 (i+1)) + stT240 28 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 27
    simpa using h
  have hprev := st240_p27
  have hstep := st240_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p29 : ((286844240489/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT240 (i+1))
      = (∑ i ∈ Finset.range 28, stT240 (i+1)) + stT240 29 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 28
    simpa using h
  have hprev := st240_p28
  have hstep := st240_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p30 : ((3259421783109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT240 (i+1))
      = (∑ i ∈ Finset.range 29, stT240 (i+1)) + stT240 30 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 29
    simpa using h
  have hprev := st240_p29
  have hstep := st240_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p31 : ((3191541718233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT240 (i+1))
      = (∑ i ∈ Finset.range 30, stT240 (i+1)) + stT240 31 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 30
    simpa using h
  have hprev := st240_p30
  have hstep := st240_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p32 : ((1457719380167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT240 (i+1))
      = (∑ i ∈ Finset.range 31, stT240 (i+1)) + stT240 32 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 31
    simpa using h
  have hprev := st240_p31
  have hstep := st240_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p33 : ((23937948737/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT240 (i+1))
      = (∑ i ∈ Finset.range 32, stT240 (i+1)) + stT240 33 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 32
    simpa using h
  have hprev := st240_p32
  have hstep := st240_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p34 : ((375406576401/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT240 (i+1))
      = (∑ i ∈ Finset.range 33, stT240 (i+1)) + stT240 34 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 33
    simpa using h
  have hprev := st240_p33
  have hstep := st240_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p35 : ((1032115743867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT240 (i+1))
      = (∑ i ∈ Finset.range 34, stT240 (i+1)) + stT240 35 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 34
    simpa using h
  have hprev := st240_p34
  have hstep := st240_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p36 : ((115518932337/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT240 (i+1))
      = (∑ i ∈ Finset.range 35, stT240 (i+1)) + stT240 36 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 35
    simpa using h
  have hprev := st240_p35
  have hstep := st240_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p37 : ((5333915307477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT240 (i+1))
      = (∑ i ∈ Finset.range 36, stT240 (i+1)) + stT240 37 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 36
    simpa using h
  have hprev := st240_p36
  have hstep := st240_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p38 : ((1384296412173/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT240 (i+1))
      = (∑ i ∈ Finset.range 37, stT240 (i+1)) + stT240 38 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 37
    simpa using h
  have hprev := st240_p37
  have hstep := st240_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p39 : ((21257007733/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT240 (i+1))
      = (∑ i ∈ Finset.range 38, stT240 (i+1)) + stT240 39 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 38
    simpa using h
  have hprev := st240_p38
  have hstep := st240_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p40 : ((5040975220229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT240 (i+1))
      = (∑ i ∈ Finset.range 39, stT240 (i+1)) + stT240 40 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 39
    simpa using h
  have hprev := st240_p39
  have hstep := st240_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p41 : ((5758284147803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT240 (i+1))
      = (∑ i ∈ Finset.range 40, stT240 (i+1)) + stT240 41 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 40
    simpa using h
  have hprev := st240_p40
  have hstep := st240_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p42 : ((12468510101263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT240 (i+1))
      = (∑ i ∈ Finset.range 41, stT240 (i+1)) + stT240 42 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 41
    simpa using h
  have hprev := st240_p41
  have hstep := st240_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p43 : ((6256351320789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT240 (i+1))
      = (∑ i ∈ Finset.range 42, stT240 (i+1)) + stT240 43 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 42
    simpa using h
  have hprev := st240_p42
  have hstep := st240_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p44 : ((11499809767089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT240 (i+1))
      = (∑ i ∈ Finset.range 43, stT240 (i+1)) + stT240 44 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 43
    simpa using h
  have hprev := st240_p43
  have hstep := st240_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p45 : ((10011326381529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT240 (i+1))
      = (∑ i ∈ Finset.range 44, stT240 (i+1)) + stT240 45 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 44
    simpa using h
  have hprev := st240_p44
  have hstep := st240_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p46 : ((9295392262129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT240 (i+1))
      = (∑ i ∈ Finset.range 45, stT240 (i+1)) + stT240 46 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 45
    simpa using h
  have hprev := st240_p45
  have hstep := st240_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p47 : ((10136560132853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT240 (i+1))
      = (∑ i ∈ Finset.range 46, stT240 (i+1)) + stT240 47 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 46
    simpa using h
  have hprev := st240_p46
  have hstep := st240_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p48 : ((11525906719853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT240 (i+1))
      = (∑ i ∈ Finset.range 47, stT240 (i+1)) + stT240 48 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 47
    simpa using h
  have hprev := st240_p47
  have hstep := st240_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p49 : ((11471463840933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT240 (i+1))
      = (∑ i ∈ Finset.range 48, stT240 (i+1)) + stT240 49 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 48
    simpa using h
  have hprev := st240_p48
  have hstep := st240_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p50 : ((10063994227499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT240 (i+1))
      = (∑ i ∈ Finset.range 49, stT240 (i+1)) + stT240 50 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 49
    simpa using h
  have hprev := st240_p49
  have hstep := st240_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p51 : ((4935337816741/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT240 (i+1))
      = (∑ i ∈ Finset.range 50, stT240 (i+1)) + stT240 51 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 50
    simpa using h
  have hprev := st240_p50
  have hstep := st240_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p52 : ((5626091859241/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT240 (i+1))
      = (∑ i ∈ Finset.range 51, stT240 (i+1)) + stT240 52 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 51
    simpa using h
  have hprev := st240_p51
  have hstep := st240_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p53 : ((5588702303921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT240 (i+1))
      = (∑ i ∈ Finset.range 52, stT240 (i+1)) + stT240 53 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 52
    simpa using h
  have hprev := st240_p52
  have hstep := st240_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p54 : ((4934885006767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT240 (i+1))
      = (∑ i ∈ Finset.range 53, stT240 (i+1)) + stT240 54 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 53
    simpa using h
  have hprev := st240_p53
  have hstep := st240_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p55 : ((10619122531799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT240 (i+1))
      = (∑ i ∈ Finset.range 54, stT240 (i+1)) + stT240 55 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 54
    simpa using h
  have hprev := st240_p54
  have hstep := st240_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p56 : ((11366450325993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT240 (i+1))
      = (∑ i ∈ Finset.range 55, stT240 (i+1)) + stT240 56 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 55
    simpa using h
  have hprev := st240_p55
  have hstep := st240_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p57 : ((10052865915771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT240 (i+1))
      = (∑ i ∈ Finset.range 56, stT240 (i+1)) + stT240 57 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 56
    simpa using h
  have hprev := st240_p56
  have hstep := st240_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p58 : ((10575359029587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT240 (i+1))
      = (∑ i ∈ Finset.range 57, stT240 (i+1)) + stT240 58 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 57
    simpa using h
  have hprev := st240_p57
  have hstep := st240_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p59 : ((11257728526269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT240 (i+1))
      = (∑ i ∈ Finset.range 58, stT240 (i+1)) + stT240 59 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 58
    simpa using h
  have hprev := st240_p58
  have hstep := st240_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p60 : ((9977053740299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT240 (i+1))
      = (∑ i ∈ Finset.range 59, stT240 (i+1)) + stT240 60 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 59
    simpa using h
  have hprev := st240_p59
  have hstep := st240_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p61 : ((10957492975563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT240 (i+1))
      = (∑ i ∈ Finset.range 60, stT240 (i+1)) + stT240 61 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 60
    simpa using h
  have hprev := st240_p60
  have hstep := st240_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p62 : ((10816303043217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT240 (i+1))
      = (∑ i ∈ Finset.range 61, stT240 (i+1)) + stT240 62 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 61
    simpa using h
  have hprev := st240_p61
  have hstep := st240_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p63 : ((2023655352011/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT240 (i+1))
      = (∑ i ∈ Finset.range 62, stT240 (i+1)) + stT240 63 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 62
    simpa using h
  have hprev := st240_p62
  have hstep := st240_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p64 : ((2258857102011/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT240 (i+1))
      = (∑ i ∈ Finset.range 63, stT240 (i+1)) + stT240 64 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 63
    simpa using h
  have hprev := st240_p63
  have hstep := st240_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p65 : ((2017522591651/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT240 (i+1))
      = (∑ i ∈ Finset.range 64, stT240 (i+1)) + stT240 65 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 64
    simpa using h
  have hprev := st240_p64
  have hstep := st240_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p66 : ((10982829630347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT240 (i+1))
      = (∑ i ∈ Finset.range 65, stT240 (i+1)) + stT240 66 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 65
    simpa using h
  have hprev := st240_p65
  have hstep := st240_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p67 : ((10567392245597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT240 (i+1))
      = (∑ i ∈ Finset.range 66, stT240 (i+1)) + stT240 67 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 66
    simpa using h
  have hprev := st240_p66
  have hstep := st240_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p68 : ((10486004507191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT240 (i+1))
      = (∑ i ∈ Finset.range 67, stT240 (i+1)) + stT240 68 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 67
    simpa using h
  have hprev := st240_p67
  have hstep := st240_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p69 : ((10986958713583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT240 (i+1))
      = (∑ i ∈ Finset.range 68, stT240 (i+1)) + stT240 69 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 68
    simpa using h
  have hprev := st240_p68
  have hstep := st240_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p70 : ((10180150453087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT240 (i+1))
      = (∑ i ∈ Finset.range 69, stT240 (i+1)) + stT240 70 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 69
    simpa using h
  have hprev := st240_p69
  have hstep := st240_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p71 : ((11181060186429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT240 (i+1))
      = (∑ i ∈ Finset.range 70, stT240 (i+1)) + stT240 71 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 70
    simpa using h
  have hprev := st240_p70
  have hstep := st240_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p72 : ((2014953008953/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT240 (i+1))
      = (∑ i ∈ Finset.range 71, stT240 (i+1)) + stT240 72 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 71
    simpa using h
  have hprev := st240_p71
  have hstep := st240_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p73 : ((175398807401/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT240 (i+1))
      = (∑ i ∈ Finset.range 72, stT240 (i+1)) + stT240 73 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 72
    simpa using h
  have hprev := st240_p72
  have hstep := st240_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p74 : ((10065044971627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT240 (i+1))
      = (∑ i ∈ Finset.range 73, stT240 (i+1)) + stT240 74 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 73
    simpa using h
  have hprev := st240_p73
  have hstep := st240_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p75 : ((11219445904327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT240 (i+1))
      = (∑ i ∈ Finset.range 74, stT240 (i+1)) + stT240 75 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 74
    simpa using h
  have hprev := st240_p74
  have hstep := st240_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p76 : ((629638714807/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT240 (i+1))
      = (∑ i ∈ Finset.range 75, stT240 (i+1)) + stT240 76 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 75
    simpa using h
  have hprev := st240_p75
  have hstep := st240_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p77 : ((11212141240327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT240 (i+1))
      = (∑ i ∈ Finset.range 76, stT240 (i+1)) + stT240 77 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 76
    simpa using h
  have hprev := st240_p76
  have hstep := st240_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p78 : ((10079848520713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT240 (i+1))
      = (∑ i ∈ Finset.range 77, stT240 (i+1)) + stT240 78 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 77
    simpa using h
  have hprev := st240_p77
  have hstep := st240_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p79 : ((5600833571489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT240 (i+1))
      = (∑ i ∈ Finset.range 78, stT240 (i+1)) + stT240 79 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 78
    simpa using h
  have hprev := st240_p78
  have hstep := st240_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p80 : ((1263184801163/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT240 (i+1))
      = (∑ i ∈ Finset.range 79, stT240 (i+1)) + stT240 80 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 79
    simpa using h
  have hprev := st240_p79
  have hstep := st240_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p81 : ((2229182549941/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT240 (i+1))
      = (∑ i ∈ Finset.range 80, stT240 (i+1)) + stT240 81 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 80
    simpa using h
  have hprev := st240_p80
  have hstep := st240_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p82 : ((2041485272369/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT240 (i+1))
      = (∑ i ∈ Finset.range 81, stT240 (i+1)) + stT240 82 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 81
    simpa using h
  have hprev := st240_p81
  have hstep := st240_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p83 : ((10981751324893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT240 (i+1))
      = (∑ i ∈ Finset.range 82, stT240 (i+1)) + stT240 83 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 82
    simpa using h
  have hprev := st240_p82
  have hstep := st240_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p84 : ((10443534085333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT240 (i+1))
      = (∑ i ∈ Finset.range 83, stT240 (i+1)) + stT240 84 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 83
    simpa using h
  have hprev := st240_p83
  have hstep := st240_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p85 : ((10674336099761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT240 (i+1))
      = (∑ i ∈ Finset.range 84, stT240 (i+1)) + stT240 85 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 84
    simpa using h
  have hprev := st240_p84
  have hstep := st240_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p86 : ((5401724791553/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT240 (i+1))
      = (∑ i ∈ Finset.range 85, stT240 (i+1)) + stT240 86 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 85
    simpa using h
  have hprev := st240_p85
  have hstep := st240_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p87 : ((10301624579083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT240 (i+1))
      = (∑ i ∈ Finset.range 86, stT240 (i+1)) + stT240 87 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 86
    simpa using h
  have hprev := st240_p86
  have hstep := st240_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p88 : ((695442283757/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT240 (i+1))
      = (∑ i ∈ Finset.range 87, stT240 (i+1)) + stT240 88 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 87
    simpa using h
  have hprev := st240_p87
  have hstep := st240_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p89 : ((2525347668843/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT240 (i+1))
      = (∑ i ∈ Finset.range 88, stT240 (i+1)) + stT240 89 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 88
    simpa using h
  have hprev := st240_p88
  have hstep := st240_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p90 : ((2783357240637/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT240 (i+1))
      = (∑ i ∈ Finset.range 89, stT240 (i+1)) + stT240 90 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 89
    simpa using h
  have hprev := st240_p89
  have hstep := st240_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p91 : ((10327768477513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT240 (i+1))
      = (∑ i ∈ Finset.range 90, stT240 (i+1)) + stT240 91 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 90
    simpa using h
  have hprev := st240_p90
  have hstep := st240_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p92 : ((10692913681933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT240 (i+1))
      = (∑ i ∈ Finset.range 91, stT240 (i+1)) + stT240 92 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 91
    simpa using h
  have hprev := st240_p91
  have hstep := st240_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p93 : ((1088778477251/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT240 (i+1))
      = (∑ i ∈ Finset.range 92, stT240 (i+1)) + stT240 93 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 92
    simpa using h
  have hprev := st240_p92
  have hstep := st240_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p94 : ((635894500781/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT240 (i+1))
      = (∑ i ∈ Finset.range 93, stT240 (i+1)) + stT240 94 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 93
    simpa using h
  have hprev := st240_p93
  have hstep := st240_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p95 : ((2794684579657/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT240 (i+1))
      = (∑ i ∈ Finset.range 94, stT240 (i+1)) + stT240 95 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 94
    simpa using h
  have hprev := st240_p94
  have hstep := st240_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p96 : ((10248188142499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT240 (i+1))
      = (∑ i ∈ Finset.range 95, stT240 (i+1)) + stT240 96 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 95
    simpa using h
  have hprev := st240_p95
  have hstep := st240_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p97 : ((2145712916127/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT240 (i+1))
      = (∑ i ∈ Finset.range 96, stT240 (i+1)) + stT240 97 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 96
    simpa using h
  have hprev := st240_p96
  have hstep := st240_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p98 : ((10916463964307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT240 (i+1))
      = (∑ i ∈ Finset.range 97, stT240 (i+1)) + stT240 98 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 97
    simpa using h
  have hprev := st240_p97
  have hstep := st240_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p99 : ((10134056956877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT240 (i+1))
      = (∑ i ∈ Finset.range 98, stT240 (i+1)) + stT240 99 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 98
    simpa using h
  have hprev := st240_p98
  have hstep := st240_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p100 : ((5566355479111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT240 (i+1))
      = (∑ i ∈ Finset.range 99, stT240 (i+1)) + stT240 100 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 99
    simpa using h
  have hprev := st240_p99
  have hstep := st240_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p101 : ((652659475399/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT240 (i+1))
      = (∑ i ∈ Finset.range 100, stT240 (i+1)) + stT240 101 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 100
    simpa using h
  have hprev := st240_p100
  have hstep := st240_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p102 : ((81499788009/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT240 (i+1))
      = (∑ i ∈ Finset.range 101, stT240 (i+1)) + stT240 102 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 101
    simpa using h
  have hprev := st240_p101
  have hstep := st240_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p103 : ((11146102867179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT240 (i+1))
      = (∑ i ∈ Finset.range 102, stT240 (i+1)) + stT240 103 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 102
    simpa using h
  have hprev := st240_p102
  have hstep := st240_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p104 : ((5083699839897/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT240 (i+1))
      = (∑ i ∈ Finset.range 103, stT240 (i+1)) + stT240 104 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 103
    simpa using h
  have hprev := st240_p103
  have hstep := st240_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p105 : ((5384070149097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT240 (i+1))
      = (∑ i ∈ Finset.range 104, stT240 (i+1)) + stT240 105 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 104
    simpa using h
  have hprev := st240_p104
  have hstep := st240_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p106 : ((5482204900357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT240 (i+1))
      = (∑ i ∈ Finset.range 105, stT240 (i+1)) + stT240 106 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 105
    simpa using h
  have hprev := st240_p105
  have hstep := st240_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p107 : ((10106528353651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT240 (i+1))
      = (∑ i ∈ Finset.range 106, stT240 (i+1)) + stT240 107 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 106
    simpa using h
  have hprev := st240_p106
  have hstep := st240_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p108 : ((10981218414901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT240 (i+1))
      = (∑ i ∈ Finset.range 107, stT240 (i+1)) + stT240 108 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 107
    simpa using h
  have hprev := st240_p107
  have hstep := st240_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p109 : ((10780187768487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT240 (i+1))
      = (∑ i ∈ Finset.range 108, stT240 (i+1)) + stT240 109 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 108
    simpa using h
  have hprev := st240_p108
  have hstep := st240_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p110 : ((10138366056963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT240 (i+1))
      = (∑ i ∈ Finset.range 109, stT240 (i+1)) + stT240 110 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 109
    simpa using h
  have hprev := st240_p109
  have hstep := st240_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p111 : ((1107855447247/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT240 (i+1))
      = (∑ i ∈ Finset.range 110, stT240 (i+1)) + stT240 111 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 110
    simpa using h
  have hprev := st240_p110
  have hstep := st240_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p112 : ((5336112652027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT240 (i+1))
      = (∑ i ∈ Finset.range 111, stT240 (i+1)) + stT240 112 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 111
    simpa using h
  have hprev := st240_p111
  have hstep := st240_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p113 : ((10169474839303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT240 (i+1))
      = (∑ i ∈ Finset.range 112, stT240 (i+1)) + stT240 113 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 112
    simpa using h
  have hprev := st240_p112
  have hstep := st240_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p114 : ((2776456189117/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT240 (i+1))
      = (∑ i ∈ Finset.range 113, stT240 (i+1)) + stT240 114 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 113
    simpa using h
  have hprev := st240_p113
  have hstep := st240_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p115 : ((10654409343523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT240 (i+1))
      = (∑ i ∈ Finset.range 114, stT240 (i+1)) + stT240 115 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 114
    simpa using h
  have hprev := st240_p114
  have hstep := st240_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p116 : ((317575670357/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT240 (i+1))
      = (∑ i ∈ Finset.range 115, stT240 (i+1)) + stT240 116 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 115
    simpa using h
  have hprev := st240_p115
  have hstep := st240_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p117 : ((692791835589/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT240 (i+1))
      = (∑ i ∈ Finset.range 116, stT240 (i+1)) + stT240 117 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 116
    simpa using h
  have hprev := st240_p116
  have hstep := st240_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p118 : ((5361932363687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT240 (i+1))
      = (∑ i ∈ Finset.range 117, stT240 (i+1)) + stT240 118 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 117
    simpa using h
  have hprev := st240_p117
  have hstep := st240_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p119 : ((2024756695657/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT240 (i+1))
      = (∑ i ∈ Finset.range 118, stT240 (i+1)) + stT240 119 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 118
    simpa using h
  have hprev := st240_p118
  have hstep := st240_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p120 : ((2200411323631/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT240 (i+1))
      = (∑ i ∈ Finset.range 119, stT240 (i+1)) + stT240 120 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 119
    simpa using h
  have hprev := st240_p119
  have hstep := st240_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p121 : ((2717683923983/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT240 (i+1))
      = (∑ i ∈ Finset.range 120, stT240 (i+1)) + stT240 121 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 120
    simpa using h
  have hprev := st240_p120
  have hstep := st240_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p122 : ((5049291056557/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT240 (i+1))
      = (∑ i ∈ Finset.range 121, stT240 (i+1)) + stT240 122 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 121
    simpa using h
  have hprev := st240_p121
  have hstep := st240_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p123 : ((2706382776077/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT240 (i+1))
      = (∑ i ∈ Finset.range 122, stT240 (i+1)) + stT240 123 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 122
    simpa using h
  have hprev := st240_p122
  have hstep := st240_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p124 : ((552836484703/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT240 (i+1))
      = (∑ i ∈ Finset.range 123, stT240 (i+1)) + stT240 124 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 123
    simpa using h
  have hprev := st240_p123
  have hstep := st240_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p125 : ((2541604462929/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT240 (i+1))
      = (∑ i ∈ Finset.range 124, stT240 (i+1)) + stT240 125 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 124
    simpa using h
  have hprev := st240_p124
  have hstep := st240_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p126 : ((2636067863379/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT240 (i+1))
      = (∑ i ∈ Finset.range 125, stT240 (i+1)) + stT240 126 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 125
    simpa using h
  have hprev := st240_p125
  have hstep := st240_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p127 : ((2796165076577/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT240 (i+1))
      = (∑ i ∈ Finset.range 126, stT240 (i+1)) + stT240 127 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 126
    simpa using h
  have hprev := st240_p126
  have hstep := st240_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p128 : ((32520976423/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT240 (i+1))
      = (∑ i ∈ Finset.range 127, stT240 (i+1)) + stT240 128 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 127
    simpa using h
  have hprev := st240_p127
  have hstep := st240_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p129 : ((25584127517/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT240 (i+1))
      = (∑ i ∈ Finset.range 128, stT240 (i+1)) + stT240 129 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 128
    simpa using h
  have hprev := st240_p128
  have hstep := st240_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p130 : ((2776880444507/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT240 (i+1))
      = (∑ i ∈ Finset.range 129, stT240 (i+1)) + stT240 130 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 129
    simpa using h
  have hprev := st240_p129
  have hstep := st240_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p131 : ((10805437400573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT240 (i+1))
      = (∑ i ∈ Finset.range 130, stT240 (i+1)) + stT240 131 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 130
    simpa using h
  have hprev := st240_p130
  have hstep := st240_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p132 : ((10090633915879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT240 (i+1))
      = (∑ i ∈ Finset.range 131, stT240 (i+1)) + stT240 132 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 131
    simpa using h
  have hprev := st240_p131
  have hstep := st240_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p133 : ((2685196543579/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT240 (i+1))
      = (∑ i ∈ Finset.range 132, stT240 (i+1)) + stT240 133 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 132
    simpa using h
  have hprev := st240_p132
  have hstep := st240_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p134 : ((2787969191803/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT240 (i+1))
      = (∑ i ∈ Finset.range 133, stT240 (i+1)) + stT240 134 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 133
    simpa using h
  have hprev := st240_p133
  have hstep := st240_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p135 : ((1032526675947/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT240 (i+1))
      = (∑ i ∈ Finset.range 134, stT240 (i+1)) + stT240 135 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 134
    simpa using h
  have hprev := st240_p134
  have hstep := st240_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p136 : ((10254994350627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT240 (i+1))
      = (∑ i ∈ Finset.range 135, stT240 (i+1)) + stT240 136 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 135
    simpa using h
  have hprev := st240_p135
  have hstep := st240_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p137 : ((694035060683/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT240 (i+1))
      = (∑ i ∈ Finset.range 136, stT240 (i+1)) + stT240 137 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 136
    simpa using h
  have hprev := st240_p136
  have hstep := st240_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p138 : ((21228837061/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT240 (i+1))
      = (∑ i ∈ Finset.range 137, stT240 (i+1)) + stT240 138 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 137
    simpa using h
  have hprev := st240_p137
  have hstep := st240_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p139 : ((10102519617503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT240 (i+1))
      = (∑ i ∈ Finset.range 138, stT240 (i+1)) + stT240 139 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 138
    simpa using h
  have hprev := st240_p138
  have hstep := st240_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p140 : ((10573983705479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT240 (i+1))
      = (∑ i ∈ Finset.range 139, stT240 (i+1)) + stT240 140 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 139
    simpa using h
  have hprev := st240_p139
  have hstep := st240_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p141 : ((11201925177119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT240 (i+1))
      = (∑ i ∈ Finset.range 140, stT240 (i+1)) + stT240 141 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 140
    simpa using h
  have hprev := st240_p140
  have hstep := st240_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p142 : ((10568904179877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT240 (i+1))
      = (∑ i ∈ Finset.range 141, stT240 (i+1)) + stT240 142 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 141
    simpa using h
  have hprev := st240_p141
  have hstep := st240_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p143 : ((10094746036447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT240 (i+1))
      = (∑ i ∈ Finset.range 142, stT240 (i+1)) + stT240 143 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 142
    simpa using h
  have hprev := st240_p142
  have hstep := st240_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p144 : ((10825565744119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT240 (i+1))
      = (∑ i ∈ Finset.range 143, stT240 (i+1)) + stT240 144 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 143
    simpa using h
  have hprev := st240_p143
  have hstep := st240_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p145 : ((2231465426879/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT240 (i+1))
      = (∑ i ∈ Finset.range 144, stT240 (i+1)) + stT240 145 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 144
    simpa using h
  have hprev := st240_p144
  have hstep := st240_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p146 : ((10374959733567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT240 (i+1))
      = (∑ i ∈ Finset.range 145, stT240 (i+1)) + stT240 146 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 145
    simpa using h
  have hprev := st240_p145
  have hstep := st240_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p147 : ((5079489267693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT240 (i+1))
      = (∑ i ∈ Finset.range 146, stT240 (i+1)) + stT240 147 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 146
    simpa using h
  have hprev := st240_p146
  have hstep := st240_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p148 : ((5481558590859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT240 (i+1))
      = (∑ i ∈ Finset.range 147, stT240 (i+1)) + stT240 148 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 147
    simpa using h
  have hprev := st240_p147
  have hstep := st240_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p149 : ((5548083424983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT240 (i+1))
      = (∑ i ∈ Finset.range 148, stT240 (i+1)) + stT240 149 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 148
    simpa using h
  have hprev := st240_p148
  have hstep := st240_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p150 : ((10286375739827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT240 (i+1))
      = (∑ i ∈ Finset.range 149, stT240 (i+1)) + stT240 150 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 149
    simpa using h
  have hprev := st240_p149
  have hstep := st240_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p151 : ((10201259920739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT240 (i+1))
      = (∑ i ∈ Finset.range 150, stT240 (i+1)) + stT240 151 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 150
    simpa using h
  have hprev := st240_p150
  have hstep := st240_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p152 : ((2752235809523/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT240 (i+1))
      = (∑ i ∈ Finset.range 151, stT240 (i+1)) + stT240 152 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 151
    simpa using h
  have hprev := st240_p151
  have hstep := st240_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p153 : ((692516403011/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT240 (i+1))
      = (∑ i ∈ Finset.range 152, stT240 (i+1)) + stT240 153 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 152
    simpa using h
  have hprev := st240_p152
  have hstep := st240_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p154 : ((10278082573959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT240 (i+1))
      = (∑ i ∈ Finset.range 153, stT240 (i+1)) + stT240 154 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 153
    simpa using h
  have hprev := st240_p153
  have hstep := st240_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p155 : ((10187434377639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT240 (i+1))
      = (∑ i ∈ Finset.range 154, stT240 (i+1)) + stT240 155 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 154
    simpa using h
  have hprev := st240_p154
  have hstep := st240_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p156 : ((10980152845479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT240 (i+1))
      = (∑ i ∈ Finset.range 155, stT240 (i+1)) + stT240 156 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 155
    simpa using h
  have hprev := st240_p155
  have hstep := st240_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p157 : ((11121165064647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT240 (i+1))
      = (∑ i ∈ Finset.range 156, stT240 (i+1)) + stT240 157 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 156
    simpa using h
  have hprev := st240_p156
  have hstep := st240_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p158 : ((10345559659287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT240 (i+1))
      = (∑ i ∈ Finset.range 157, stT240 (i+1)) + stT240 158 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 157
    simpa using h
  have hprev := st240_p157
  have hstep := st240_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p159 : ((10125404458827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT240 (i+1))
      = (∑ i ∈ Finset.range 158, stT240 (i+1)) + stT240 159 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 158
    simpa using h
  have hprev := st240_p158
  have hstep := st240_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p160 : ((5434360970133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT240 (i+1))
      = (∑ i ∈ Finset.range 159, stT240 (i+1)) + stT240 160 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 159
    simpa using h
  have hprev := st240_p159
  have hstep := st240_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p161 : ((1399008562397/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT240 (i+1))
      = (∑ i ∈ Finset.range 160, stT240 (i+1)) + stT240 161 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 160
    simpa using h
  have hprev := st240_p160
  have hstep := st240_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p162 : ((2626347922969/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT240 (i+1))
      = (∑ i ∈ Finset.range 161, stT240 (i+1)) + stT240 162 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 161
    simpa using h
  have hprev := st240_p161
  have hstep := st240_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p163 : ((5031094860557/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT240 (i+1))
      = (∑ i ∈ Finset.range 162, stT240 (i+1)) + stT240 163 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 162
    simpa using h
  have hprev := st240_p162
  have hstep := st240_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p164 : ((5328611034633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT240 (i+1))
      = (∑ i ∈ Finset.range 163, stT240 (i+1)) + stT240 164 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 163
    simpa using h
  have hprev := st240_p163
  have hstep := st240_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p165 : ((5612161804177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT240 (i+1))
      = (∑ i ∈ Finset.range 164, stT240 (i+1)) + stT240 165 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 164
    simpa using h
  have hprev := st240_p164
  have hstep := st240_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p166 : ((10764506142971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT240 (i+1))
      = (∑ i ∈ Finset.range 165, stT240 (i+1)) + stT240 166 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 165
    simpa using h
  have hprev := st240_p165
  have hstep := st240_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p167 : ((403484674547/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT240 (i+1))
      = (∑ i ∈ Finset.range 166, stT240 (i+1)) + stT240 167 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 166
    simpa using h
  have hprev := st240_p166
  have hstep := st240_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p168 : ((2072740298419/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT240 (i+1))
      = (∑ i ∈ Finset.range 167, stT240 (i+1)) + stT240 168 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 167
    simpa using h
  have hprev := st240_p167
  have hstep := st240_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p169 : ((2222861686759/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT240 (i+1))
      = (∑ i ∈ Finset.range 168, stT240 (i+1)) + stT240 169 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 168
    simpa using h
  have hprev := st240_p168
  have hstep := st240_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p170 : ((2212829784559/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT240 (i+1))
      = (∑ i ∈ Finset.range 169, stT240 (i+1)) + stT240 170 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 169
    simpa using h
  have hprev := st240_p169
  have hstep := st240_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p171 : ((2060608597903/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT240 (i+1))
      = (∑ i ∈ Finset.range 170, stT240 (i+1)) + stT240 171 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 170
    simpa using h
  have hprev := st240_p170
  have hstep := st240_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p172 : ((10100244251291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT240 (i+1))
      = (∑ i ∈ Finset.range 171, stT240 (i+1)) + stT240 172 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 171
    simpa using h
  have hprev := st240_p171
  have hstep := st240_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p173 : ((10785248871731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT240 (i+1))
      = (∑ i ∈ Finset.range 172, stT240 (i+1)) + stT240 173 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 172
    simpa using h
  have hprev := st240_p172
  have hstep := st240_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p174 : ((2247120610683/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT240 (i+1))
      = (∑ i ∈ Finset.range 173, stT240 (i+1)) + stT240 174 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 173
    simpa using h
  have hprev := st240_p173
  have hstep := st240_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p175 : ((536314605501/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT240 (i+1))
      = (∑ i ∈ Finset.range 174, stT240 (i+1)) + stT240 175 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 174
    simpa using h
  have hprev := st240_p174
  have hstep := st240_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p176 : ((5039080633551/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT240 (i+1))
      = (∑ i ∈ Finset.range 175, stT240 (i+1)) + stT240 176 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 175
    simpa using h
  have hprev := st240_p175
  have hstep := st240_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p177 : ((515904070439/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT240 (i+1))
      = (∑ i ∈ Finset.range 176, stT240 (i+1)) + stT240 177 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 176
    simpa using h
  have hprev := st240_p176
  have hstep := st240_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p178 : ((11063348326921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT240 (i+1))
      = (∑ i ∈ Finset.range 177, stT240 (i+1)) + stT240 178 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 177
    simpa using h
  have hprev := st240_p177
  have hstep := st240_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p179 : ((1394098393307/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT240 (i+1))
      = (∑ i ∈ Finset.range 178, stT240 (i+1)) + stT240 179 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 178
    simpa using h
  have hprev := st240_p178
  have hstep := st240_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p180 : ((2613386766883/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT240 (i+1))
      = (∑ i ∈ Finset.range 179, stT240 (i+1)) + stT240 180 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 179
    simpa using h
  have hprev := st240_p179
  have hstep := st240_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p181 : ((5018473286261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT240 (i+1))
      = (∑ i ∈ Finset.range 180, stT240 (i+1)) + stT240 181 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 180
    simpa using h
  have hprev := st240_p180
  have hstep := st240_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p182 : ((10529788948891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT240 (i+1))
      = (∑ i ∈ Finset.range 181, stT240 (i+1)) + stT240 182 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 181
    simpa using h
  have hprev := st240_p181
  have hstep := st240_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p183 : ((447530120461/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT240 (i+1))
      = (∑ i ∈ Finset.range 182, stT240 (i+1)) + stT240 183 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 182
    simpa using h
  have hprev := st240_p182
  have hstep := st240_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p184 : ((2207081599887/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT240 (i+1))
      = (∑ i ∈ Finset.range 183, stT240 (i+1)) + stT240 184 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 183
    simpa using h
  have hprev := st240_p183
  have hstep := st240_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p185 : ((206030636519/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT240 (i+1))
      = (∑ i ∈ Finset.range 184, stT240 (i+1)) + stT240 185 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 184
    simpa using h
  have hprev := st240_p184
  have hstep := st240_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p186 : ((40232903161/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT240 (i+1))
      = (∑ i ∈ Finset.range 185, stT240 (i+1)) + stT240 186 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 185
    simpa using h
  have hprev := st240_p185
  have hstep := st240_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p187 : ((5326230902541/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT240 (i+1))
      = (∑ i ∈ Finset.range 186, stT240 (i+1)) + stT240 187 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 186
    simpa using h
  have hprev := st240_p186
  have hstep := st240_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p188 : ((5614763510787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT240 (i+1))
      = (∑ i ∈ Finset.range 187, stT240 (i+1)) + stT240 188 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 187
    simpa using h
  have hprev := st240_p187
  have hstep := st240_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p189 : ((2194606303947/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT240 (i+1))
      = (∑ i ∈ Finset.range 188, stT240 (i+1)) + stT240 189 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 188
    simpa using h
  have hprev := st240_p188
  have hstep := st240_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p190 : ((10248655793821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT240 (i+1))
      = (∑ i ∈ Finset.range 189, stT240 (i+1)) + stT240 190 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 189
    simpa using h
  have hprev := st240_p189
  have hstep := st240_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p191 : ((157283513339/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT240 (i+1))
      = (∑ i ∈ Finset.range 190, stT240 (i+1)) + stT240 191 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 190
    simpa using h
  have hprev := st240_p190
  have hstep := st240_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p192 : ((10672730715753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT240 (i+1))
      = (∑ i ∈ Finset.range 191, stT240 (i+1)) + stT240 192 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 191
    simpa using h
  have hprev := st240_p191
  have hstep := st240_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p193 : ((11234985410403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT240 (i+1))
      = (∑ i ∈ Finset.range 192, stT240 (i+1)) + stT240 193 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 192
    simpa using h
  have hprev := st240_p192
  have hstep := st240_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p194 : ((5496475331059/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT240 (i+1))
      = (∑ i ∈ Finset.range 193, stT240 (i+1)) + stT240 194 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 193
    simpa using h
  have hprev := st240_p193
  have hstep := st240_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p195 : ((1284602130391/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT240 (i+1))
      = (∑ i ∈ Finset.range 194, stT240 (i+1)) + stT240 195 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 194
    simpa using h
  have hprev := st240_p194
  have hstep := st240_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p196 : ((5020556688709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT240 (i+1))
      = (∑ i ∈ Finset.range 195, stT240 (i+1)) + stT240 196 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 195
    simpa using h
  have hprev := st240_p195
  have hstep := st240_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p197 : ((2648133986537/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT240 (i+1))
      = (∑ i ∈ Finset.range 196, stT240 (i+1)) + stT240 197 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 196
    simpa using h
  have hprev := st240_p196
  have hstep := st240_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p198 : ((11205834054451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT240 (i+1))
      = (∑ i ∈ Finset.range 197, stT240 (i+1)) + stT240 198 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 197
    simpa using h
  have hprev := st240_p197
  have hstep := st240_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p199 : ((11087391214363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT240 (i+1))
      = (∑ i ∈ Finset.range 198, stT240 (i+1)) + stT240 199 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 198
    simpa using h
  have hprev := st240_p198
  have hstep := st240_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p200 : ((649646299651/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT240 (i+1))
      = (∑ i ∈ Finset.range 199, stT240 (i+1)) + stT240 200 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 199
    simpa using h
  have hprev := st240_p199
  have hstep := st240_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p201 : ((2502863750963/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT240 (i+1))
      = (∑ i ∈ Finset.range 200, stT240 (i+1)) + stT240 201 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 200
    simpa using h
  have hprev := st240_p200
  have hstep := st240_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p202 : ((5209343548547/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT240 (i+1))
      = (∑ i ∈ Finset.range 201, stT240 (i+1)) + stT240 202 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 201
    simpa using h
  have hprev := st240_p201
  have hstep := st240_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p203 : ((1110175884763/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT240 (i+1))
      = (∑ i ∈ Finset.range 202, stT240 (i+1)) + stT240 203 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 202
    simpa using h
  have hprev := st240_p202
  have hstep := st240_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p204 : ((1121308950931/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT240 (i+1))
      = (∑ i ∈ Finset.range 203, stT240 (i+1)) + stT240 204 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 203
    simpa using h
  have hprev := st240_p203
  have hstep := st240_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p205 : ((5310085938671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT240 (i+1))
      = (∑ i ∈ Finset.range 204, stT240 (i+1)) + stT240 205 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 204
    simpa using h
  have hprev := st240_p204
  have hstep := st240_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p206 : ((62809000819/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT240 (i+1))
      = (∑ i ∈ Finset.range 205, stT240 (i+1)) + stT240 206 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 205
    simpa using h
  have hprev := st240_p205
  have hstep := st240_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p207 : ((127363875333/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT240 (i+1))
      = (∑ i ∈ Finset.range 206, stT240 (i+1)) + stT240 207 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 206
    simpa using h
  have hprev := st240_p206
  have hstep := st240_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p208 : ((2173391656053/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT240 (i+1))
      = (∑ i ∈ Finset.range 207, stT240 (i+1)) + stT240 208 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 207
    simpa using h
  have hprev := st240_p207
  have hstep := st240_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p209 : ((11275277746179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT240 (i+1))
      = (∑ i ∈ Finset.range 208, stT240 (i+1)) + stT240 209 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 208
    simpa using h
  have hprev := st240_p208
  have hstep := st240_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p210 : ((10935903287379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT240 (i+1))
      = (∑ i ∈ Finset.range 209, stT240 (i+1)) + stT240 210 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 209
    simpa using h
  have hprev := st240_p209
  have hstep := st240_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p211 : ((10249835598849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT240 (i+1))
      = (∑ i ∈ Finset.range 210, stT240 (i+1)) + stT240 211 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 210
    simpa using h
  have hprev := st240_p210
  have hstep := st240_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p212 : ((1251577159583/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT240 (i+1))
      = (∑ i ∈ Finset.range 211, stT240 (i+1)) + stT240 212 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 211
    simpa using h
  have hprev := st240_p211
  have hstep := st240_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p213 : ((655806580423/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT240 (i+1))
      = (∑ i ∈ Finset.range 212, stT240 (i+1)) + stT240 213 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 212
    simpa using h
  have hprev := st240_p212
  have hstep := st240_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p214 : ((1392442302001/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT240 (i+1))
      = (∑ i ∈ Finset.range 213, stT240 (i+1)) + stT240 214 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 213
    simpa using h
  have hprev := st240_p213
  have hstep := st240_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p215 : ((1402792924939/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT240 (i+1))
      = (∑ i ∈ Finset.range 214, stT240 (i+1)) + stT240 215 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 214
    simpa using h
  have hprev := st240_p214
  have hstep := st240_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p216 : ((213054927729/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT240 (i+1))
      = (∑ i ∈ Finset.range 215, stT240 (i+1)) + stT240 216 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 215
    simpa using h
  have hprev := st240_p215
  have hstep := st240_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p217 : ((402675447213/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT240 (i+1))
      = (∑ i ∈ Finset.range 216, stT240 (i+1)) + stT240 217 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 216
    simpa using h
  have hprev := st240_p216
  have hstep := st240_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p218 : ((80872269007/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT240 (i+1))
      = (∑ i ∈ Finset.range 217, stT240 (i+1)) + stT240 218 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 217
    simpa using h
  have hprev := st240_p217
  have hstep := st240_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p219 : ((10728714187303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT240 (i+1))
      = (∑ i ∈ Finset.range 218, stT240 (i+1)) + stT240 219 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 218
    simpa using h
  have hprev := st240_p218
  have hstep := st240_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p220 : ((5625753821837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT240 (i+1))
      = (∑ i ∈ Finset.range 219, stT240 (i+1)) + stT240 220 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 219
    simpa using h
  have hprev := st240_p219
  have hstep := st240_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p221 : ((11117191662399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT240 (i+1))
      = (∑ i ∈ Finset.range 220, stT240 (i+1)) + stT240 221 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 220
    simpa using h
  have hprev := st240_p220
  have hstep := st240_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p222 : ((5236661617431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT240 (i+1))
      = (∑ i ∈ Finset.range 221, stT240 (i+1)) + stT240 222 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 221
    simpa using h
  have hprev := st240_p221
  have hstep := st240_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p223 : ((5001536788031/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT240 (i+1))
      = (∑ i ∈ Finset.range 222, stT240 (i+1)) + stT240 223 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 222
    simpa using h
  have hprev := st240_p222
  have hstep := st240_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p224 : ((5098769085203/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT240 (i+1))
      = (∑ i ∈ Finset.range 223, stT240 (i+1)) + stT240 224 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 223
    simpa using h
  have hprev := st240_p223
  have hstep := st240_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p225 : ((5425012758959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT240 (i+1))
      = (∑ i ∈ Finset.range 224, stT240 (i+1)) + stT240 225 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 224
    simpa using h
  have hprev := st240_p224
  have hstep := st240_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p226 : ((5642515919969/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT240 (i+1))
      = (∑ i ∈ Finset.range 225, stT240 (i+1)) + stT240 226 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 225
    simpa using h
  have hprev := st240_p225
  have hstep := st240_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p227 : ((5529720672237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT240 (i+1))
      = (∑ i ∈ Finset.range 226, stT240 (i+1)) + stT240 227 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 226
    simpa using h
  have hprev := st240_p226
  have hstep := st240_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p228 : ((10406588469879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT240 (i+1))
      = (∑ i ∈ Finset.range 227, stT240 (i+1)) + stT240 228 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 227
    simpa using h
  have hprev := st240_p227
  have hstep := st240_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p229 : ((1997227683243/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT240 (i+1))
      = (∑ i ∈ Finset.range 228, stT240 (i+1)) + stT240 229 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 228
    simpa using h
  have hprev := st240_p228
  have hstep := st240_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p230 : ((2043205986891/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT240 (i+1))
      = (∑ i ∈ Finset.range 229, stT240 (i+1)) + stT240 230 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 229
    simpa using h
  have hprev := st240_p229
  have hstep := st240_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p231 : ((10864081403709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT240 (i+1))
      = (∑ i ∈ Finset.range 230, stT240 (i+1)) + stT240 231 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 230
    simpa using h
  have hprev := st240_p230
  have hstep := st240_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p232 : ((11290747763337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT240 (i+1))
      = (∑ i ∈ Finset.range 231, stT240 (i+1)) + stT240 232 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 231
    simpa using h
  have hprev := st240_p231
  have hstep := st240_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p233 : ((11081669507769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT240 (i+1))
      = (∑ i ∈ Finset.range 232, stT240 (i+1)) + stT240 233 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 232
    simpa using h
  have hprev := st240_p232
  have hstep := st240_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p234 : ((2088682586349/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT240 (i+1))
      = (∑ i ∈ Finset.range 233, stT240 (i+1)) + stT240 234 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 233
    simpa using h
  have hprev := st240_p233
  have hstep := st240_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p235 : ((4995687840117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT240 (i+1))
      = (∑ i ∈ Finset.range 234, stT240 (i+1)) + stT240 235 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 234
    simpa using h
  have hprev := st240_p234
  have hstep := st240_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p236 : ((5077327934709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT240 (i+1))
      = (∑ i ∈ Finset.range 235, stT240 (i+1)) + stT240 236 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 235
    simpa using h
  have hprev := st240_p235
  have hstep := st240_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p237 : ((5387358124443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT240 (i+1))
      = (∑ i ∈ Finset.range 236, stT240 (i+1)) + stT240 237 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 236
    simpa using h
  have hprev := st240_p236
  have hstep := st240_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p238 : ((11267053003709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT240 (i+1))
      = (∑ i ∈ Finset.range 237, stT240 (i+1)) + stT240 238 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 237
    simpa using h
  have hprev := st240_p237
  have hstep := st240_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p239 : ((11174445212413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT240 (i+1))
      = (∑ i ∈ Finset.range 238, stT240 (i+1)) + stT240 239 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 238
    simpa using h
  have hprev := st240_p238
  have hstep := st240_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p240 : ((10586362968517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT240 (i+1))
      = (∑ i ∈ Finset.range 239, stT240 (i+1)) + stT240 240 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 239
    simpa using h
  have hprev := st240_p239
  have hstep := st240_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p241 : ((10045000542577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT240 (i+1))
      = (∑ i ∈ Finset.range 240, stT240 (i+1)) + stT240 241 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 240
    simpa using h
  have hprev := st240_p240
  have hstep := st240_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p242 : ((5021142946301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT240 (i+1))
      = (∑ i ∈ Finset.range 241, stT240 (i+1)) + stT240 242 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 241
    simpa using h
  have hprev := st240_p241
  have hstep := st240_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p243 : ((5288490316551/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT240 (i+1))
      = (∑ i ∈ Finset.range 242, stT240 (i+1)) + stT240 243 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 242
    simpa using h
  have hprev := st240_p242
  have hstep := st240_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p244 : ((5583254716959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT240 (i+1))
      = (∑ i ∈ Finset.range 243, stT240 (i+1)) + stT240 244 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 243
    simpa using h
  have hprev := st240_p243
  have hstep := st240_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p245 : ((1128641815373/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT240 (i+1))
      = (∑ i ∈ Finset.range 244, stT240 (i+1)) + stT240 245 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 244
    simpa using h
  have hprev := st240_p244
  have hstep := st240_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p246 : ((1083404452069/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT240 (i+1))
      = (∑ i ∈ Finset.range 245, stT240 (i+1)) + stT240 246 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 245
    simpa using h
  have hprev := st240_p245
  have hstep := st240_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p247 : ((12761711471/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT240 (i+1))
      = (∑ i ∈ Finset.range 246, stT240 (i+1)) + stT240 247 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 246
    simpa using h
  have hprev := st240_p246
  have hstep := st240_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p248 : ((4978250174291/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT240 (i+1))
      = (∑ i ∈ Finset.range 247, stT240 (i+1)) + stT240 248 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 247
    simpa using h
  have hprev := st240_p247
  have hstep := st240_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p249 : ((5145543170707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT240 (i+1))
      = (∑ i ∈ Finset.range 248, stT240 (i+1)) + stT240 249 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 248
    simpa using h
  have hprev := st240_p248
  have hstep := st240_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p250 : ((5461317832927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT240 (i+1))
      = (∑ i ∈ Finset.range 249, stT240 (i+1)) + stT240 250 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 249
    simpa using h
  have hprev := st240_p249
  have hstep := st240_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p251 : ((5656119449983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT240 (i+1))
      = (∑ i ∈ Finset.range 250, stT240 (i+1)) + stT240 251 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 250
    simpa using h
  have hprev := st240_p250
  have hstep := st240_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p252 : ((278317548383/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT240 (i+1))
      = (∑ i ∈ Finset.range 251, stT240 (i+1)) + stT240 252 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 251
    simpa using h
  have hprev := st240_p251
  have hstep := st240_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p253 : ((2107634421541/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT240 (i+1))
      = (∑ i ∈ Finset.range 252, stT240 (i+1)) + stT240 253 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 252
    simpa using h
  have hprev := st240_p252
  have hstep := st240_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p254 : ((2005160189989/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT240 (i+1))
      = (∑ i ∈ Finset.range 253, stT240 (i+1)) + stT240 254 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 253
    simpa using h
  have hprev := st240_p253
  have hstep := st240_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p255 : ((250450878343/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT240 (i+1))
      = (∑ i ∈ Finset.range 254, stT240 (i+1)) + stT240 255 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 254
    simpa using h
  have hprev := st240_p254
  have hstep := st240_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p256 : ((131473587609/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT240 (i+1))
      = (∑ i ∈ Finset.range 255, stT240 (i+1)) + stT240 256 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 255
    simpa using h
  have hprev := st240_p255
  have hstep := st240_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p257 : ((5557629975093/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT240 (i+1))
      = (∑ i ∈ Finset.range 256, stT240 (i+1)) + stT240 257 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 256
    simpa using h
  have hprev := st240_p256
  have hstep := st240_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p258 : ((5663447915361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT240 (i+1))
      = (∑ i ∈ Finset.range 257, stT240 (i+1)) + stT240 258 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 257
    simpa using h
  have hprev := st240_p257
  have hstep := st240_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p259 : ((5492770625131/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT240 (i+1))
      = (∑ i ∈ Finset.range 258, stT240 (i+1)) + stT240 259 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 258
    simpa using h
  have hprev := st240_p258
  have hstep := st240_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p260 : ((1295827732783/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT240 (i+1))
      = (∑ i ∈ Finset.range 259, stT240 (i+1)) + stT240 260 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 259
    simpa using h
  have hprev := st240_p259
  have hstep := st240_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p261 : ((4980648433297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT240 (i+1))
      = (∑ i ∈ Finset.range 260, stT240 (i+1)) + stT240 261 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 260
    simpa using h
  have hprev := st240_p260
  have hstep := st240_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p262 : ((126079581961/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT240 (i+1))
      = (∑ i ∈ Finset.range 261, stT240 (i+1)) + stT240 262 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 261
    simpa using h
  have hprev := st240_p261
  have hstep := st240_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p263 : ((5320435901881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT240 (i+1))
      = (∑ i ∈ Finset.range 262, stT240 (i+1)) + stT240 263 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 262
    simpa using h
  have hprev := st240_p262
  have hstep := st240_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p264 : ((5596405589767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT240 (i+1))
      = (∑ i ∈ Finset.range 263, stT240 (i+1)) + stT240 264 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 263
    simpa using h
  have hprev := st240_p263
  have hstep := st240_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p265 : ((11317962114179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT240 (i+1))
      = (∑ i ∈ Finset.range 264, stT240 (i+1)) + stT240 265 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 264
    simpa using h
  have hprev := st240_p264
  have hstep := st240_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p266 : ((10923526086479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT240 (i+1))
      = (∑ i ∈ Finset.range 265, stT240 (i+1)) + stT240 266 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 265
    simpa using h
  have hprev := st240_p265
  have hstep := st240_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p267 : ((412470118211/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT240 (i+1))
      = (∑ i ∈ Finset.range 266, stT240 (i+1)) + stT240 267 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 266
    simpa using h
  have hprev := st240_p266
  have hstep := st240_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p268 : ((9944429284043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT240 (i+1))
      = (∑ i ∈ Finset.range 267, stT240 (i+1)) + stT240 268 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 267
    simpa using h
  have hprev := st240_p267
  have hstep := st240_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p269 : ((10094504522863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT240 (i+1))
      = (∑ i ∈ Finset.range 268, stT240 (i+1)) + stT240 269 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 268
    simpa using h
  have hprev := st240_p268
  have hstep := st240_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p270 : ((10647270433903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT240 (i+1))
      = (∑ i ∈ Finset.range 269, stT240 (i+1)) + stT240 270 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 269
    simpa using h
  have hprev := st240_p269
  have hstep := st240_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p271 : ((11192693027183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT240 (i+1))
      = (∑ i ∈ Finset.range 270, stT240 (i+1)) + stT240 271 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 270
    simpa using h
  have hprev := st240_p270
  have hstep := st240_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p272 : ((11331528893369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT240 (i+1))
      = (∑ i ∈ Finset.range 271, stT240 (i+1)) + stT240 272 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 271
    simpa using h
  have hprev := st240_p271
  have hstep := st240_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p273 : ((10965390162489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT240 (i+1))
      = (∑ i ∈ Finset.range 272, stT240 (i+1)) + stT240 273 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 272
    simpa using h
  have hprev := st240_p272
  have hstep := st240_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p274 : ((161903304333/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT240 (i+1))
      = (∑ i ∈ Finset.range 273, stT240 (i+1)) + stT240 274 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 273
    simpa using h
  have hprev := st240_p273
  have hstep := st240_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p275 : ((9955122514721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT240 (i+1))
      = (∑ i ∈ Finset.range 274, stT240 (i+1)) + stT240 275 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 274
    simpa using h
  have hprev := st240_p274
  have hstep := st240_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p276 : ((10033746480701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT240 (i+1))
      = (∑ i ∈ Finset.range 275, stT240 (i+1)) + stT240 276 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 275
    simpa using h
  have hprev := st240_p275
  have hstep := st240_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p277 : ((1053899908517/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT240 (i+1))
      = (∑ i ∈ Finset.range 276, stT240 (i+1)) + stT240 277 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 276
    simpa using h
  have hprev := st240_p276
  have hstep := st240_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p278 : ((1111314753389/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT240 (i+1))
      = (∑ i ∈ Finset.range 277, stT240 (i+1)) + stT240 278 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 277
    simpa using h
  have hprev := st240_p277
  have hstep := st240_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p279 : ((5677505839551/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT240 (i+1))
      = (∑ i ∈ Finset.range 278, stT240 (i+1)) + stT240 279 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 278
    simpa using h
  have hprev := st240_p278
  have hstep := st240_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p280 : ((5549470411491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT240 (i+1))
      = (∑ i ∈ Finset.range 279, stT240 (i+1)) + stT240 280 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 279
    simpa using h
  have hprev := st240_p279
  have hstep := st240_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p281 : ((164443161813/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT240 (i+1))
      = (∑ i ∈ Finset.range 280, stT240 (i+1)) + stT240 281 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 280
    simpa using h
  have hprev := st240_p280
  have hstep := st240_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p282 : ((1253284075063/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT240 (i+1))
      = (∑ i ∈ Finset.range 281, stT240 (i+1)) + stT240 282 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 281
    simpa using h
  have hprev := st240_p281
  have hstep := st240_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p283 : ((9942645138667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT240 (i+1))
      = (∑ i ∈ Finset.range 282, stT240 (i+1)) + stT240 283 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 282
    simpa using h
  have hprev := st240_p282
  have hstep := st240_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p284 : ((10327367171607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT240 (i+1))
      = (∑ i ∈ Finset.range 283, stT240 (i+1)) + stT240 284 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 283
    simpa using h
  have hprev := st240_p283
  have hstep := st240_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p285 : ((10919545760079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT240 (i+1))
      = (∑ i ∈ Finset.range 284, stT240 (i+1)) + stT240 285 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 284
    simpa using h
  have hprev := st240_p284
  have hstep := st240_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p286 : ((2264679178131/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT240 (i+1))
      = (∑ i ∈ Finset.range 285, stT240 (i+1)) + stT240 286 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 285
    simpa using h
  have hprev := st240_p285
  have hstep := st240_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p287 : ((11272780980001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT240 (i+1))
      = (∑ i ∈ Finset.range 286, stT240 (i+1)) + stT240 287 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 286
    simpa using h
  have hprev := st240_p286
  have hstep := st240_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p288 : ((10803734971769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT240 (i+1))
      = (∑ i ∈ Finset.range 287, stT240 (i+1)) + stT240 288 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 287
    simpa using h
  have hprev := st240_p287
  have hstep := st240_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p289 : ((10225148983349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT240 (i+1))
      = (∑ i ∈ Finset.range 288, stT240 (i+1)) + stT240 289 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 288
    simpa using h
  have hprev := st240_p288
  have hstep := st240_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p290 : ((4956572479983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT240 (i+1))
      = (∑ i ∈ Finset.range 289, stT240 (i+1)) + stT240 290 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 289
    simpa using h
  have hprev := st240_p289
  have hstep := st240_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p291 : ((5033621577543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT240 (i+1))
      = (∑ i ∈ Finset.range 290, stT240 (i+1)) + stT240 291 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 290
    simpa using h
  have hprev := st240_p290
  have hstep := st240_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p292 : ((5292954002883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT240 (i+1))
      = (∑ i ∈ Finset.range 291, stT240 (i+1)) + stT240 292 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 291
    simpa using h
  have hprev := st240_p291
  have hstep := st240_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p293 : ((2784203711993/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT240 (i+1))
      = (∑ i ∈ Finset.range 292, stT240 (i+1)) + stT240 293 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 292
    simpa using h
  have hprev := st240_p292
  have hstep := st240_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p294 : ((11371387561071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT240 (i+1))
      = (∑ i ∈ Finset.range 293, stT240 (i+1)) + stT240 294 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 293
    simpa using h
  have hprev := st240_p293
  have hstep := st240_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p295 : ((696507191647/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT240 (i+1))
      = (∑ i ∈ Finset.range 294, stT240 (i+1)) + stT240 295 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 294
    simpa using h
  have hprev := st240_p294
  have hstep := st240_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p296 : ((2649906661461/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT240 (i+1))
      = (∑ i ∈ Finset.range 295, stT240 (i+1)) + stT240 296 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 295
    simpa using h
  have hprev := st240_p295
  have hstep := st240_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p297 : ((5038779749959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT240 (i+1))
      = (∑ i ∈ Finset.range 296, stT240 (i+1)) + stT240 297 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 296
    simpa using h
  have hprev := st240_p296
  have hstep := st240_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p298 : ((38670130193/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT240 (i+1))
      = (∑ i ∈ Finset.range 297, stT240 (i+1)) + stT240 298 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 297
    simpa using h
  have hprev := st240_p297
  have hstep := st240_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p299 : ((5086289708503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT240 (i+1))
      = (∑ i ∈ Finset.range 298, stT240 (i+1)) + stT240 299 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 298
    simpa using h
  have hprev := st240_p298
  have hstep := st240_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p300 : ((5363888826103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT240 (i+1))
      = (∑ i ∈ Finset.range 299, stT240 (i+1)) + stT240 300 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 299
    simpa using h
  have hprev := st240_p299
  have hstep := st240_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p301 : ((5613839773213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT240 (i+1))
      = (∑ i ∈ Finset.range 300, stT240 (i+1)) + stT240 301 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 300
    simpa using h
  have hprev := st240_p300
  have hstep := st240_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p302 : ((1421517812897/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT240 (i+1))
      = (∑ i ∈ Finset.range 301, stT240 (i+1)) + stT240 302 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 301
    simpa using h
  have hprev := st240_p301
  have hstep := st240_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p303 : ((5538479735753/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT240 (i+1))
      = (∑ i ∈ Finset.range 302, stT240 (i+1)) + stT240 303 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 302
    simpa using h
  have hprev := st240_p302
  have hstep := st240_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p304 : ((5259945196613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT240 (i+1))
      = (∑ i ∈ Finset.range 303, stT240 (i+1)) + stT240 304 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 303
    simpa using h
  have hprev := st240_p303
  have hstep := st240_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p305 : ((156734763053/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT240 (i+1))
      = (∑ i ∈ Finset.range 304, stT240 (i+1)) + stT240 305 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 304
    simpa using h
  have hprev := st240_p304
  have hstep := st240_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p306 : ((4948259527537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT240 (i+1))
      = (∑ i ∈ Finset.range 305, stT240 (i+1)) + stT240 306 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 305
    simpa using h
  have hprev := st240_p305
  have hstep := st240_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p307 : ((5096320016327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT240 (i+1))
      = (∑ i ∈ Finset.range 306, stT240 (i+1)) + stT240 307 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 306
    simpa using h
  have hprev := st240_p306
  have hstep := st240_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p308 : ((5372715581873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT240 (i+1))
      = (∑ i ∈ Finset.range 307, stT240 (i+1)) + stT240 308 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 307
    simpa using h
  have hprev := st240_p307
  have hstep := st240_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p309 : ((5617656536833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT240 (i+1))
      = (∑ i ∈ Finset.range 308, stT240 (i+1)) + stT240 309 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 308
    simpa using h
  have hprev := st240_p308
  have hstep := st240_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p310 : ((11382478016337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT240 (i+1))
      = (∑ i ∈ Finset.range 309, stT240 (i+1)) + stT240 310 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 309
    simpa using h
  have hprev := st240_p309
  have hstep := st240_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p311 : ((11105226701313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT240 (i+1))
      = (∑ i ∈ Finset.range 310, stT240 (i+1)) + stT240 311 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 310
    simpa using h
  have hprev := st240_p310
  have hstep := st240_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p312 : ((264065594949/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT240 (i+1))
      = (∑ i ∈ Finset.range 311, stT240 (i+1)) + stT240 312 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 311
    simpa using h
  have hprev := st240_p311
  have hstep := st240_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p313 : ((1257604522999/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT240 (i+1))
      = (∑ i ∈ Finset.range 312, stT240 (i+1)) + stT240 313 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 312
    simpa using h
  have hprev := st240_p312
  have hstep := st240_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p314 : ((9879661024673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT240 (i+1))
      = (∑ i ∈ Finset.range 313, stT240 (i+1)) + stT240 314 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 313
    simpa using h
  have hprev := st240_p313
  have hstep := st240_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p315 : ((10117760063297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT240 (i+1))
      = (∑ i ∈ Finset.range 314, stT240 (i+1)) + stT240 315 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 314
    simpa using h
  have hprev := st240_p314
  have hstep := st240_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p316 : ((10641441467771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT240 (i+1))
      = (∑ i ∈ Finset.range 315, stT240 (i+1)) + stT240 316 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 315
    simpa using h
  have hprev := st240_p315
  have hstep := st240_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p317 : ((11162051843681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT240 (i+1))
      = (∑ i ∈ Finset.range 316, stT240 (i+1)) + stT240 317 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 316
    simpa using h
  have hprev := st240_p316
  have hstep := st240_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p318 : ((11395973958077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT240 (i+1))
      = (∑ i ∈ Finset.range 317, stT240 (i+1)) + stT240 318 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 317
    simpa using h
  have hprev := st240_p317
  have hstep := st240_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p319 : ((11218123946627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT240 (i+1))
      = (∑ i ∈ Finset.range 318, stT240 (i+1)) + stT240 319 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 318
    simpa using h
  have hprev := st240_p318
  have hstep := st240_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p320 : ((10726563528017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT240 (i+1))
      = (∑ i ∈ Finset.range 319, stT240 (i+1)) + stT240 320 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 319
    simpa using h
  have hprev := st240_p319
  have hstep := st240_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p321 : ((10186073918581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT240 (i+1))
      = (∑ i ∈ Finset.range 320, stT240 (i+1)) + stT240 321 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 320
    simpa using h
  have hprev := st240_p320
  have hstep := st240_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p322 : ((9884429941461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT240 (i+1))
      = (∑ i ∈ Finset.range 321, stT240 (i+1)) + stT240 322 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 321
    simpa using h
  have hprev := st240_p321
  have hstep := st240_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p323 : ((1995958858667/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT240 (i+1))
      = (∑ i ∈ Finset.range 322, stT240 (i+1)) + stT240 323 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 322
    simpa using h
  have hprev := st240_p322
  have hstep := st240_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p324 : ((2083960103999/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT240 (i+1))
      = (∑ i ∈ Finset.range 323, stT240 (i+1)) + stT240 324 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 323
    simpa using h
  have hprev := st240_p323
  have hstep := st240_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p325 : ((2194512923399/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT240 (i+1))
      = (∑ i ∈ Finset.range 324, stT240 (i+1)) + stT240 325 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 324
    simpa using h
  have hprev := st240_p324
  have hstep := st240_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p326 : ((2270052805967/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT240 (i+1))
      = (∑ i ∈ Finset.range 325, stT240 (i+1)) + stT240 326 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 325
    simpa using h
  have hprev := st240_p325
  have hstep := st240_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p327 : ((11358768079213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT240 (i+1))
      = (∑ i ∈ Finset.range 326, stT240 (i+1)) + stT240 327 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 326
    simpa using h
  have hprev := st240_p326
  have hstep := st240_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p328 : ((10995731372267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT240 (i+1))
      = (∑ i ∈ Finset.range 327, stT240 (i+1)) + stT240 328 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 327
    simpa using h
  have hprev := st240_p327
  have hstep := st240_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p329 : ((417941511289/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT240 (i+1))
      = (∑ i ∈ Finset.range 328, stT240 (i+1)) + stT240 329 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 328
    simpa using h
  have hprev := st240_p328
  have hstep := st240_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p330 : ((399836708791/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT240 (i+1))
      = (∑ i ∈ Finset.range 329, stT240 (i+1)) + stT240 330 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 329
    simpa using h
  have hprev := st240_p329
  have hstep := st240_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p331 : ((394629698453/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT240 (i+1))
      = (∑ i ∈ Finset.range 330, stT240 (i+1)) + stT240 331 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 330
    simpa using h
  have hprev := st240_p330
  have hstep := st240_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p332 : ((5060773141481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT240 (i+1))
      = (∑ i ∈ Finset.range 331, stT240 (i+1)) + stT240 332 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 331
    simpa using h
  have hprev := st240_p331
  have hstep := st240_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p333 : ((5316798790667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT240 (i+1))
      = (∑ i ∈ Finset.range 332, stT240 (i+1)) + stT240 333 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 332
    simpa using h
  have hprev := st240_p332
  have hstep := st240_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p334 : ((11146517784809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT240 (i+1))
      = (∑ i ∈ Finset.range 333, stT240 (i+1)) + stT240 334 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 333
    simpa using h
  have hprev := st240_p333
  have hstep := st240_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p335 : ((11407333249627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT240 (i+1))
      = (∑ i ∈ Finset.range 334, stT240 (i+1)) + stT240 335 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 334
    simpa using h
  have hprev := st240_p334
  have hstep := st240_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p336 : ((1411189464349/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT240 (i+1))
      = (∑ i ∈ Finset.range 335, stT240 (i+1)) + stT240 336 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 335
    simpa using h
  have hprev := st240_p335
  have hstep := st240_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p337 : ((10852538558287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT240 (i+1))
      = (∑ i ∈ Finset.range 336, stT240 (i+1)) + stT240 337 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 336
    simpa using h
  have hprev := st240_p336
  have hstep := st240_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p338 : ((1288744880767/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT240 (i+1))
      = (∑ i ∈ Finset.range 337, stT240 (i+1)) + stT240 338 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 337
    simpa using h
  have hprev := st240_p337
  have hstep := st240_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p339 : ((2480972197889/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT240 (i+1))
      = (∑ i ∈ Finset.range 338, stT240 (i+1)) + stT240 339 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 338
    simpa using h
  have hprev := st240_p338
  have hstep := st240_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p340 : ((987852964593/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT240 (i+1))
      = (∑ i ∈ Finset.range 339, stT240 (i+1)) + stT240 340 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 339
    simpa using h
  have hprev := st240_p339
  have hstep := st240_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p341 : ((509682757947/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT240 (i+1))
      = (∑ i ∈ Finset.range 340, stT240 (i+1)) + stT240 341 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 340
    simpa using h
  have hprev := st240_p340
  have hstep := st240_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p342 : ((1071797364957/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT240 (i+1))
      = (∑ i ∈ Finset.range 341, stT240 (i+1)) + stT240 342 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 341
    simpa using h
  have hprev := st240_p341
  have hstep := st240_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p343 : ((11203229595513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT240 (i+1))
      = (∑ i ∈ Finset.range 342, stT240 (i+1)) + stT240 343 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 342
    simpa using h
  have hprev := st240_p342
  have hstep := st240_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p344 : ((11422184768139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT240 (i+1))
      = (∑ i ∈ Finset.range 343, stT240 (i+1)) + stT240 344 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 343
    simpa using h
  have hprev := st240_p343
  have hstep := st240_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p345 : ((11274183556339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT240 (i+1))
      = (∑ i ∈ Finset.range 344, stT240 (i+1)) + stT240 345 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 344
    simpa using h
  have hprev := st240_p344
  have hstep := st240_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p346 : ((10829765145679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT240 (i+1))
      = (∑ i ∈ Finset.range 345, stT240 (i+1)) + stT240 346 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 345
    simpa using h
  have hprev := st240_p345
  have hstep := st240_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p347 : ((10295325034729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT240 (i+1))
      = (∑ i ∈ Finset.range 346, stT240 (i+1)) + stT240 347 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 346
    simpa using h
  have hprev := st240_p346
  have hstep := st240_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p348 : ((2479077153291/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT240 (i+1))
      = (∑ i ∈ Finset.range 347, stT240 (i+1)) + stT240 348 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 347
    simpa using h
  have hprev := st240_p347
  have hstep := st240_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p349 : ((2466168683171/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT240 (i+1))
      = (∑ i ∈ Finset.range 348, stT240 (i+1)) + stT240 349 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 348
    simpa using h
  have hprev := st240_p348
  have hstep := st240_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p350 : ((15878269367/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT240 (i+1))
      = (∑ i ∈ Finset.range 349, stT240 (i+1)) + stT240 350 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 349
    simpa using h
  have hprev := st240_p349
  have hstep := st240_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p351 : ((16675976189/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT240 (i+1))
      = (∑ i ∈ Finset.range 350, stT240 (i+1)) + stT240 351 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 350
    simpa using h
  have hprev := st240_p350
  have hstep := st240_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p352 : ((11166210870011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT240 (i+1))
      = (∑ i ∈ Finset.range 351, stT240 (i+1)) + stT240 352 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 351
    simpa using h
  have hprev := st240_p351
  have hstep := st240_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p353 : ((456911926027/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT240 (i+1))
      = (∑ i ∈ Finset.range 352, stT240 (i+1)) + stT240 353 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 352
    simpa using h
  have hprev := st240_p352
  have hstep := st240_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p354 : ((566489512307/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT240 (i+1))
      = (∑ i ∈ Finset.range 353, stT240 (i+1)) + stT240 354 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 353
    simpa using h
  have hprev := st240_p353
  have hstep := st240_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p355 : ((218600641013/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT240 (i+1))
      = (∑ i ∈ Finset.range 354, stT240 (i+1)) + stT240 355 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 354
    simpa using h
  have hprev := st240_p354
  have hstep := st240_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p356 : ((10400492559783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT240 (i+1))
      = (∑ i ∈ Finset.range 355, stT240 (i+1)) + stT240 356 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 355
    simpa using h
  have hprev := st240_p355
  have hstep := st240_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p357 : ((1246615676499/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT240 (i+1))
      = (∑ i ∈ Finset.range 356, stT240 (i+1)) + stT240 357 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 356
    simpa using h
  have hprev := st240_p356
  have hstep := st240_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p358 : ((9832382699869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT240 (i+1))
      = (∑ i ∈ Finset.range 357, stT240 (i+1)) + stT240 358 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 357
    simpa using h
  have hprev := st240_p357
  have hstep := st240_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p359 : ((10038053953937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT240 (i+1))
      = (∑ i ∈ Finset.range 358, stT240 (i+1)) + stT240 359 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 358
    simpa using h
  have hprev := st240_p358
  have hstep := st240_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p360 : ((10499835320711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT240 (i+1))
      = (∑ i ∈ Finset.range 359, stT240 (i+1)) + stT240 360 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 359
    simpa using h
  have hprev := st240_p359
  have hstep := st240_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p361 : ((2754789030169/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT240 (i+1))
      = (∑ i ∈ Finset.range 360, stT240 (i+1)) + stT240 361 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 360
    simpa using h
  have hprev := st240_p360
  have hstep := st240_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p362 : ((2843767925041/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT240 (i+1))
      = (∑ i ∈ Finset.range 361, stT240 (i+1)) + stT240 362 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 361
    simpa using h
  have hprev := st240_p361
  have hstep := st240_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p363 : ((713624687269/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT240 (i+1))
      = (∑ i ∈ Finset.range 362, stT240 (i+1)) + stT240 363 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 362
    simpa using h
  have hprev := st240_p362
  have hstep := st240_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p364 : ((11131463314923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT240 (i+1))
      = (∑ i ∈ Finset.range 363, stT240 (i+1)) + stT240 364 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 363
    simpa using h
  have hprev := st240_p363
  have hstep := st240_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p365 : ((10636944881899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT240 (i+1))
      = (∑ i ∈ Finset.range 364, stT240 (i+1)) + stT240 365 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 364
    simpa using h
  have hprev := st240_p364
  have hstep := st240_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p366 : ((10141174212923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT240 (i+1))
      = (∑ i ∈ Finset.range 365, stT240 (i+1)) + stT240 366 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 365
    simpa using h
  have hprev := st240_p365
  have hstep := st240_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p367 : ((9849276659703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT240 (i+1))
      = (∑ i ∈ Finset.range 366, stT240 (i+1)) + stT240 367 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 366
    simpa using h
  have hprev := st240_p366
  have hstep := st240_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p368 : ((9880357816167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT240 (i+1))
      = (∑ i ∈ Finset.range 367, stT240 (i+1)) + stT240 368 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 367
    simpa using h
  have hprev := st240_p367
  have hstep := st240_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p369 : ((10220056436827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT240 (i+1))
      = (∑ i ∈ Finset.range 368, stT240 (i+1)) + stT240 369 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 368
    simpa using h
  have hprev := st240_p368
  have hstep := st240_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p370 : ((10728455716077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT240 (i+1))
      = (∑ i ∈ Finset.range 369, stT240 (i+1)) + stT240 370 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 369
    simpa using h
  have hprev := st240_p369
  have hstep := st240_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p371 : ((11198705354187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT240 (i+1))
      = (∑ i ∈ Finset.range 370, stT240 (i+1)) + stT240 371 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 370
    simpa using h
  have hprev := st240_p370
  have hstep := st240_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p372 : ((11441435647137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT240 (i+1))
      = (∑ i ∈ Finset.range 371, stT240 (i+1)) + stT240 372 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 371
    simpa using h
  have hprev := st240_p371
  have hstep := st240_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p373 : ((5680216217077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT240 (i+1))
      = (∑ i ∈ Finset.range 372, stT240 (i+1)) + stT240 373 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 372
    simpa using h
  have hprev := st240_p372
  have hstep := st240_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p374 : ((5494809143797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT240 (i+1))
      = (∑ i ∈ Finset.range 373, stT240 (i+1)) + stT240 374 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 373
    simpa using h
  have hprev := st240_p373
  have hstep := st240_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p375 : ((1047757455553/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT240 (i+1))
      = (∑ i ∈ Finset.range 374, stT240 (i+1)) + stT240 375 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 374
    simpa using h
  have hprev := st240_p374
  have hstep := st240_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p376 : ((2005433092181/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT240 (i+1))
      = (∑ i ∈ Finset.range 375, stT240 (i+1)) + stT240 376 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 375
    simpa using h
  have hprev := st240_p375
  have hstep := st240_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p377 : ((9814995968039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT240 (i+1))
      = (∑ i ∈ Finset.range 376, stT240 (i+1)) + stT240 377 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 376
    simpa using h
  have hprev := st240_p376
  have hstep := st240_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p378 : ((9922800413063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT240 (i+1))
      = (∑ i ∈ Finset.range 377, stT240 (i+1)) + stT240 378 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 377
    simpa using h
  have hprev := st240_p377
  have hstep := st240_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p379 : ((5153544561589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT240 (i+1))
      = (∑ i ∈ Finset.range 378, stT240 (i+1)) + stT240 379 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 378
    simpa using h
  have hprev := st240_p378
  have hstep := st240_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p380 : ((10817831744347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT240 (i+1))
      = (∑ i ∈ Finset.range 379, stT240 (i+1)) + stT240 380 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 379
    simpa using h
  have hprev := st240_p379
  have hstep := st240_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p381 : ((5628918534151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT240 (i+1))
      = (∑ i ∈ Finset.range 380, stT240 (i+1)) + stT240 381 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 380
    simpa using h
  have hprev := st240_p380
  have hstep := st240_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p382 : ((5729473976047/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT240 (i+1))
      = (∑ i ∈ Finset.range 381, stT240 (i+1)) + stT240 382 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 381
    simpa using h
  have hprev := st240_p381
  have hstep := st240_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p383 : ((5672855680539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT240 (i+1))
      = (∑ i ∈ Finset.range 382, stT240 (i+1)) + stT240 383 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 382
    simpa using h
  have hprev := st240_p382
  have hstep := st240_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p384 : ((685159787137/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT240 (i+1))
      = (∑ i ∈ Finset.range 383, stT240 (i+1)) + stT240 384 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 383
    simpa using h
  have hprev := st240_p383
  have hstep := st240_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p385 : ((163364020537/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT240 (i+1))
      = (∑ i ∈ Finset.range 384, stT240 (i+1)) + stT240 385 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 384
    simpa using h
  have hprev := st240_p384
  have hstep := st240_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p386 : ((5007441030491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT240 (i+1))
      = (∑ i ∈ Finset.range 385, stT240 (i+1)) + stT240 386 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 385
    simpa using h
  have hprev := st240_p385
  have hstep := st240_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p387 : ((9805422554887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT240 (i+1))
      = (∑ i ∈ Finset.range 386, stT240 (i+1)) + stT240 387 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 386
    simpa using h
  have hprev := st240_p386
  have hstep := st240_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p388 : ((2475906324247/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT240 (i+1))
      = (∑ i ∈ Finset.range 387, stT240 (i+1)) + stT240 388 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 387
    simpa using h
  have hprev := st240_p387
  have hstep := st240_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p389 : ((2567923102457/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT240 (i+1))
      = (∑ i ∈ Finset.range 388, stT240 (i+1)) + stT240 389 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 388
    simpa using h
  have hprev := st240_p388
  have hstep := st240_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p390 : ((2693232213411/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT240 (i+1))
      = (∑ i ∈ Finset.range 389, stT240 (i+1)) + stT240 390 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 389
    simpa using h
  have hprev := st240_p389
  have hstep := st240_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p391 : ((11223226372091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT240 (i+1))
      = (∑ i ∈ Finset.range 390, stT240 (i+1)) + stT240 391 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 390
    simpa using h
  have hprev := st240_p390
  have hstep := st240_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p392 : ((2291762703291/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT240 (i+1))
      = (∑ i ∈ Finset.range 391, stT240 (i+1)) + stT240 392 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 391
    simpa using h
  have hprev := st240_p391
  have hstep := st240_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p393 : ((91162563271/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT240 (i+1))
      = (∑ i ∈ Finset.range 392, stT240 (i+1)) + stT240 393 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 392
    simpa using h
  have hprev := st240_p392
  have hstep := st240_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p394 : ((11057059682471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT240 (i+1))
      = (∑ i ∈ Finset.range 393, stT240 (i+1)) + stT240 394 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 393
    simpa using h
  have hprev := st240_p393
  have hstep := st240_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p395 : ((10566717021391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT240 (i+1))
      = (∑ i ∈ Finset.range 394, stT240 (i+1)) + stT240 395 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 394
    simpa using h
  have hprev := st240_p394
  have hstep := st240_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p396 : ((5050053260787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT240 (i+1))
      = (∑ i ∈ Finset.range 395, stT240 (i+1)) + stT240 396 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 395
    simpa using h
  have hprev := st240_p395
  have hstep := st240_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p397 : ((982291789509/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT240 (i+1))
      = (∑ i ∈ Finset.range 396, stT240 (i+1)) + stT240 397 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 396
    simpa using h
  have hprev := st240_p396
  have hstep := st240_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p398 : ((2458071207147/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT240 (i+1))
      = (∑ i ∈ Finset.range 397, stT240 (i+1)) + stT240 398 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 397
    simpa using h
  have hprev := st240_p397
  have hstep := st240_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p399 : ((632721626977/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT240 (i+1))
      = (∑ i ∈ Finset.range 398, stT240 (i+1)) + stT240 399 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 398
    simpa using h
  have hprev := st240_p398
  have hstep := st240_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p400 : ((662085533227/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT240 (i+1))
      = (∑ i ∈ Finset.range 399, stT240 (i+1)) + stT240 400 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 399
    simpa using h
  have hprev := st240_p399
  have hstep := st240_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p401 : ((692323186981/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT240 (i+1))
      = (∑ i ∈ Finset.range 400, stT240 (i+1)) + stT240 401 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 400
    simpa using h
  have hprev := st240_p400
  have hstep := st240_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p402 : ((2851771447527/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT240 (i+1))
      = (∑ i ∈ Finset.range 401, stT240 (i+1)) + stT240 402 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 401
    simpa using h
  have hprev := st240_p401
  have hstep := st240_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p403 : ((11469943951353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT240 (i+1))
      = (∑ i ∈ Finset.range 402, stT240 (i+1)) + stT240 403 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 402
    simpa using h
  have hprev := st240_p402
  have hstep := st240_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p404 : ((11245390740779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT240 (i+1))
      = (∑ i ∈ Finset.range 403, stT240 (i+1)) + stT240 404 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 403
    simpa using h
  have hprev := st240_p403
  have hstep := st240_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p405 : ((10811514044139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT240 (i+1))
      = (∑ i ∈ Finset.range 404, stT240 (i+1)) + stT240 405 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 404
    simpa using h
  have hprev := st240_p404
  have hstep := st240_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p406 : ((10316890081551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT240 (i+1))
      = (∑ i ∈ Finset.range 405, stT240 (i+1)) + stT240 406 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 405
    simpa using h
  have hprev := st240_p405
  have hstep := st240_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p407 : ((9929268244597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT240 (i+1))
      = (∑ i ∈ Finset.range 406, stT240 (i+1)) + stT240 407 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 406
    simpa using h
  have hprev := st240_p406
  have hstep := st240_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p408 : ((1955754337897/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT240 (i+1))
      = (∑ i ∈ Finset.range 407, stT240 (i+1)) + stT240 408 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 407
    simpa using h
  have hprev := st240_p407
  have hstep := st240_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p409 : ((9914776596289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT240 (i+1))
      = (∑ i ∈ Finset.range 408, stT240 (i+1)) + stT240 409 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 408
    simpa using h
  have hprev := st240_p408
  have hstep := st240_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p410 : ((10290557713889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT240 (i+1))
      = (∑ i ∈ Finset.range 409, stT240 (i+1)) + stT240 410 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 409
    simpa using h
  have hprev := st240_p409
  have hstep := st240_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p411 : ((5390084050687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT240 (i+1))
      = (∑ i ∈ Finset.range 410, stT240 (i+1)) + stT240 411 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 410
    simpa using h
  have hprev := st240_p410
  have hstep := st240_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p412 : ((5610593313459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT240 (i+1))
      = (∑ i ∈ Finset.range 411, stT240 (i+1)) + stT240 412 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 411
    simpa using h
  have hprev := st240_p411
  have hstep := st240_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p413 : ((229373887193/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT240 (i+1))
      = (∑ i ∈ Finset.range 412, stT240 (i+1)) + stT240 413 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 412
    simpa using h
  have hprev := st240_p412
  have hstep := st240_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p414 : ((89394441207/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT240 (i+1))
      = (∑ i ∈ Finset.range 413, stT240 (i+1)) + stT240 414 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 413
    simpa using h
  have hprev := st240_p413
  have hstep := st240_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p415 : ((2788086105897/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT240 (i+1))
      = (∑ i ∈ Finset.range 414, stT240 (i+1)) + stT240 415 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 414
    simpa using h
  have hprev := st240_p414
  have hstep := st240_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p416 : ((10693608062057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT240 (i+1))
      = (∑ i ∈ Finset.range 415, stT240 (i+1)) + stT240 416 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 415
    simpa using h
  have hprev := st240_p415
  have hstep := st240_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p417 : ((2553798546329/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT240 (i+1))
      = (∑ i ∈ Finset.range 416, stT240 (i+1)) + stT240 417 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 416
    simpa using h
  have hprev := st240_p416
  have hstep := st240_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p418 : ((616936511287/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT240 (i+1))
      = (∑ i ∈ Finset.range 417, stT240 (i+1)) + stT240 418 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 417
    simpa using h
  have hprev := st240_p417
  have hstep := st240_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p419 : ((2442627073171/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT240 (i+1))
      = (∑ i ∈ Finset.range 418, stT240 (i+1)) + stT240 419 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 418
    simpa using h
  have hprev := st240_p418
  have hstep := st240_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p420 : ((1243083059873/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT240 (i+1))
      = (∑ i ∈ Finset.range 419, stT240 (i+1)) + stT240 420 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 419
    simpa using h
  have hprev := st240_p419
  have hstep := st240_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p421 : ((1292124666123/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT240 (i+1))
      = (∑ i ∈ Finset.range 420, stT240 (i+1)) + stT240 421 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 420
    simpa using h
  have hprev := st240_p420
  have hstep := st240_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p422 : ((42276237993/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT240 (i+1))
      = (∑ i ∈ Finset.range 421, stT240 (i+1)) + stT240 422 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 421
    simpa using h
  have hprev := st240_p421
  have hstep := st240_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p423 : ((140610348459/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT240 (i+1))
      = (∑ i ∈ Finset.range 422, stT240 (i+1)) + stT240 423 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 422
    simpa using h
  have hprev := st240_p422
  have hstep := st240_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p424 : ((5741176115957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT240 (i+1))
      = (∑ i ∈ Finset.range 423, stT240 (i+1)) + stT240 424 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 423
    simpa using h
  have hprev := st240_p423
  have hstep := st240_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p425 : ((5725729968261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT240 (i+1))
      = (∑ i ∈ Finset.range 424, stT240 (i+1)) + stT240 425 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 424
    simpa using h
  have hprev := st240_p424
  have hstep := st240_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p426 : ((1116688477981/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT240 (i+1))
      = (∑ i ∈ Finset.range 425, stT240 (i+1)) + stT240 426 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 425
    simpa using h
  have hprev := st240_p425
  have hstep := st240_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p427 : ((5358754737309/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT240 (i+1))
      = (∑ i ∈ Finset.range 426, stT240 (i+1)) + stT240 427 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 426
    simpa using h
  have hprev := st240_p426
  have hstep := st240_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p428 : ((2048403201147/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT240 (i+1))
      = (∑ i ∈ Finset.range 427, stT240 (i+1)) + stT240 428 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 427
    simpa using h
  have hprev := st240_p427
  have hstep := st240_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p429 : ((1977166289007/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT240 (i+1))
      = (∑ i ∈ Finset.range 428, stT240 (i+1)) + stT240 429 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 428
    simpa using h
  have hprev := st240_p428
  have hstep := st240_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p430 : ((1219597841999/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT240 (i+1))
      = (∑ i ∈ Finset.range 429, stT240 (i+1)) + stT240 430 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 429
    simpa using h
  have hprev := st240_p429
  have hstep := st240_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p431 : ((618308573719/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT240 (i+1))
      = (∑ i ∈ Finset.range 430, stT240 (i+1)) + stT240 431 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 430
    simpa using h
  have hprev := st240_p430
  have hstep := st240_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p432 : ((5126042241377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT240 (i+1))
      = (∑ i ∈ Finset.range 431, stT240 (i+1)) + stT240 432 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 431
    simpa using h
  have hprev := st240_p431
  have hstep := st240_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p433 : ((10725452156289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT240 (i+1))
      = (∑ i ∈ Finset.range 432, stT240 (i+1)) + stT240 433 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 432
    simpa using h
  have hprev := st240_p432
  have hstep := st240_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p434 : ((2792774160561/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT240 (i+1))
      = (∑ i ∈ Finset.range 433, stT240 (i+1)) + stT240 434 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 433
    simpa using h
  have hprev := st240_p433
  have hstep := st240_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p435 : ((1432072312713/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT240 (i+1))
      = (∑ i ∈ Finset.range 434, stT240 (i+1)) + stT240 435 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 434
    simpa using h
  have hprev := st240_p434
  have hstep := st240_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p436 : ((2874513570789/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT240 (i+1))
      = (∑ i ∈ Finset.range 435, stT240 (i+1)) + stT240 436 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 435
    simpa using h
  have hprev := st240_p435
  have hstep := st240_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p437 : ((1410544166247/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT240 (i+1))
      = (∑ i ∈ Finset.range 436, stT240 (i+1)) + stT240 437 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 436
    simpa using h
  have hprev := st240_p436
  have hstep := st240_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p438 : ((2719819851453/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT240 (i+1))
      = (∑ i ∈ Finset.range 437, stT240 (i+1)) + stT240 438 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 437
    simpa using h
  have hprev := st240_p437
  have hstep := st240_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p439 : ((2600503737823/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT240 (i+1))
      = (∑ i ∈ Finset.range 438, stT240 (i+1)) + stT240 439 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 438
    simpa using h
  have hprev := st240_p438
  have hstep := st240_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p440 : ((156120145863/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT240 (i+1))
      = (∑ i ∈ Finset.range 439, stT240 (i+1)) + stT240 440 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 439
    simpa using h
  have hprev := st240_p439
  have hstep := st240_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p441 : ((9766830516459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT240 (i+1))
      = (∑ i ∈ Finset.range 440, stT240 (i+1)) + stT240 441 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 440
    simpa using h
  have hprev := st240_p440
  have hstep := st240_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p442 : ((2447866715001/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT240 (i+1))
      = (∑ i ∈ Finset.range 441, stT240 (i+1)) + stT240 442 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 441
    simpa using h
  have hprev := st240_p441
  have hstep := st240_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p443 : ((5028725677983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT240 (i+1))
      = (∑ i ∈ Finset.range 442, stT240 (i+1)) + stT240 443 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 442
    simpa using h
  have hprev := st240_p442
  have hstep := st240_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p444 : ((5243864224411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT240 (i+1))
      = (∑ i ∈ Finset.range 443, stT240 (i+1)) + stT240 444 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 443
    simpa using h
  have hprev := st240_p443
  have hstep := st240_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p445 : ((5479581204481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT240 (i+1))
      = (∑ i ∈ Finset.range 444, stT240 (i+1)) + stT240 445 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 444
    simpa using h
  have hprev := st240_p444
  have hstep := st240_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p446 : ((11338018739723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT240 (i+1))
      = (∑ i ∈ Finset.range 445, stT240 (i+1)) + stT240 446 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 445
    simpa using h
  have hprev := st240_p445
  have hstep := st240_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p447 : ((11517833632799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT240 (i+1))
      = (∑ i ∈ Finset.range 446, stT240 (i+1)) + stT240 447 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 446
    simpa using h
  have hprev := st240_p446
  have hstep := st240_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p448 : ((11448939626423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT240 (i+1))
      = (∑ i ∈ Finset.range 447, stT240 (i+1)) + stT240 448 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 447
    simpa using h
  have hprev := st240_p447
  have hstep := st240_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p449 : ((11151657705383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT240 (i+1))
      = (∑ i ∈ Finset.range 448, stT240 (i+1)) + stT240 449 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 448
    simpa using h
  have hprev := st240_p448
  have hstep := st240_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p450 : ((10709700432923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT240 (i+1))
      = (∑ i ∈ Finset.range 449, stT240 (i+1)) + stT240 450 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 449
    simpa using h
  have hprev := st240_p449
  have hstep := st240_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p451 : ((10246175022409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT240 (i+1))
      = (∑ i ∈ Finset.range 450, stT240 (i+1)) + stT240 451 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 450
    simpa using h
  have hprev := st240_p450
  have hstep := st240_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p452 : ((2472272412739/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT240 (i+1))
      = (∑ i ∈ Finset.range 451, stT240 (i+1)) + stT240 452 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 451
    simpa using h
  have hprev := st240_p451
  have hstep := st240_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p453 : ((9736122107063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT240 (i+1))
      = (∑ i ∈ Finset.range 452, stT240 (i+1)) + stT240 453 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 452
    simpa using h
  have hprev := st240_p452
  have hstep := st240_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p454 : ((4914125340643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT240 (i+1))
      = (∑ i ∈ Finset.range 453, stT240 (i+1)) + stT240 454 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 453
    simpa using h
  have hprev := st240_p453
  have hstep := st240_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p455 : ((10139358038591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT240 (i+1))
      = (∑ i ∈ Finset.range 454, stT240 (i+1)) + stT240 455 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 454
    simpa using h
  have hprev := st240_p454
  have hstep := st240_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p456 : ((423364772087/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT240 (i+1))
      = (∑ i ∈ Finset.range 455, stT240 (i+1)) + stT240 456 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 455
    simpa using h
  have hprev := st240_p455
  have hstep := st240_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p457 : ((2208367751543/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT240 (i+1))
      = (∑ i ∈ Finset.range 456, stT240 (i+1)) + stT240 457 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 456
    simpa using h
  have hprev := st240_p456
  have hstep := st240_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p458 : ((2847337729609/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT240 (i+1))
      = (∑ i ∈ Finset.range 457, stT240 (i+1)) + stT240 458 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 457
    simpa using h
  have hprev := st240_p457
  have hstep := st240_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p459 : ((2883508012219/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT240 (i+1))
      = (∑ i ∈ Finset.range 458, stT240 (i+1)) + stT240 459 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 458
    simpa using h
  have hprev := st240_p458
  have hstep := st240_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p460 : ((2859537012983/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT240 (i+1))
      = (∑ i ∈ Finset.range 459, stT240 (i+1)) + stT240 460 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 459
    simpa using h
  have hprev := st240_p459
  have hstep := st240_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p461 : ((2225627413609/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT240 (i+1))
      = (∑ i ∈ Finset.range 460, stT240 (i+1)) + stT240 461 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 460
    simpa using h
  have hprev := st240_p460
  have hstep := st240_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p462 : ((10686856874003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT240 (i+1))
      = (∑ i ∈ Finset.range 461, stT240 (i+1)) + stT240 462 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 461
    simpa using h
  have hprev := st240_p461
  have hstep := st240_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p463 : ((10231030122463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT240 (i+1))
      = (∑ i ∈ Finset.range 462, stT240 (i+1)) + stT240 463 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 462
    simpa using h
  have hprev := st240_p462
  have hstep := st240_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p464 : ((2470056632349/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT240 (i+1))
      = (∑ i ∈ Finset.range 463, stT240 (i+1)) + stT240 464 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 463
    simpa using h
  have hprev := st240_p463
  have hstep := st240_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p465 : ((4862802872269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT240 (i+1))
      = (∑ i ∈ Finset.range 464, stT240 (i+1)) + stT240 465 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 464
    simpa using h
  have hprev := st240_p464
  have hstep := st240_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p466 : ((2451637887599/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT240 (i+1))
      = (∑ i ∈ Finset.range 465, stT240 (i+1)) + stT240 466 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 465
    simpa using h
  have hprev := st240_p465
  have hstep := st240_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p467 : ((505056857863/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT240 (i+1))
      = (∑ i ∈ Finset.range 466, stT240 (i+1)) + stT240 467 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 466
    simpa using h
  have hprev := st240_p466
  have hstep := st240_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p468 : ((1053253520551/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT240 (i+1))
      = (∑ i ∈ Finset.range 467, stT240 (i+1)) + stT240 468 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 467
    simpa using h
  have hprev := st240_p467
  have hstep := st240_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p469 : ((5494711719851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT240 (i+1))
      = (∑ i ∈ Finset.range 468, stT240 (i+1)) + stT240 469 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 468
    simpa using h
  have hprev := st240_p468
  have hstep := st240_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p470 : ((709679712277/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT240 (i+1))
      = (∑ i ∈ Finset.range 469, stT240 (i+1)) + stT240 470 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 469
    simpa using h
  have hprev := st240_p469
  have hstep := st240_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p471 : ((11536205564507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT240 (i+1))
      = (∑ i ∈ Finset.range 470, stT240 (i+1)) + stT240 471 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 470
    simpa using h
  have hprev := st240_p470
  have hstep := st240_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p472 : ((11488174511707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT240 (i+1))
      = (∑ i ∈ Finset.range 471, stT240 (i+1)) + stT240 472 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 471
    simpa using h
  have hprev := st240_p471
  have hstep := st240_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p473 : ((11223833077603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT240 (i+1))
      = (∑ i ∈ Finset.range 472, stT240 (i+1)) + stT240 473 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 472
    simpa using h
  have hprev := st240_p472
  have hstep := st240_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p474 : ((2162103698727/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT240 (i+1))
      = (∑ i ∈ Finset.range 473, stT240 (i+1)) + stT240 474 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 473
    simpa using h
  have hprev := st240_p473
  have hstep := st240_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p475 : ((10352339870403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT240 (i+1))
      = (∑ i ∈ Finset.range 474, stT240 (i+1)) + stT240 475 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 474
    simpa using h
  have hprev := st240_p474
  have hstep := st240_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p476 : ((9963741573403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT240 (i+1))
      = (∑ i ∈ Finset.range 475, stT240 (i+1)) + stT240 476 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 475
    simpa using h
  have hprev := st240_p475
  have hstep := st240_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p477 : ((2435238949051/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT240 (i+1))
      = (∑ i ∈ Finset.range 476, stT240 (i+1)) + stT240 477 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 476
    simpa using h
  have hprev := st240_p476
  have hstep := st240_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p478 : ((4869215273007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT240 (i+1))
      = (∑ i ∈ Finset.range 477, stT240 (i+1)) + stT240 478 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 477
    simpa using h
  have hprev := st240_p477
  have hstep := st240_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p479 : ((4977944556033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT240 (i+1))
      = (∑ i ∈ Finset.range 478, stT240 (i+1)) + stT240 479 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 478
    simpa using h
  have hprev := st240_p478
  have hstep := st240_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p480 : ((10339108743021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT240 (i+1))
      = (∑ i ∈ Finset.range 479, stT240 (i+1)) + stT240 480 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 479
    simpa using h
  have hprev := st240_p479
  have hstep := st240_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p481 : ((10793774272581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT240 (i+1))
      = (∑ i ∈ Finset.range 480, stT240 (i+1)) + stT240 481 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 480
    simpa using h
  have hprev := st240_p480
  have hstep := st240_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p482 : ((11208952495029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT240 (i+1))
      = (∑ i ∈ Finset.range 481, stT240 (i+1)) + stT240 482 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 481
    simpa using h
  have hprev := st240_p481
  have hstep := st240_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p483 : ((11484171047869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT240 (i+1))
      = (∑ i ∈ Finset.range 482, stT240 (i+1)) + stT240 483 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 482
    simpa using h
  have hprev := st240_p482
  have hstep := st240_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p484 : ((2888384449171/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT240 (i+1))
      = (∑ i ∈ Finset.range 483, stT240 (i+1)) + stT240 484 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 483
    simpa using h
  have hprev := st240_p483
  have hstep := st240_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p485 : ((2280239265083/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT240 (i+1))
      = (∑ i ∈ Finset.range 484, stT240 (i+1)) + stT240 485 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 484
    simpa using h
  have hprev := st240_p484
  have hstep := st240_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p486 : ((2212895689429/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT240 (i+1))
      = (∑ i ∈ Finset.range 485, stT240 (i+1)) + stT240 486 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 485
    simpa using h
  have hprev := st240_p485
  have hstep := st240_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p487 : ((10624412636129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT240 (i+1))
      = (∑ i ∈ Finset.range 486, stT240 (i+1)) + stT240 487 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 486
    simpa using h
  have hprev := st240_p486
  have hstep := st240_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p488 : ((10185926028137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT240 (i+1))
      = (∑ i ∈ Finset.range 487, stT240 (i+1)) + stT240 488 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 487
    simpa using h
  have hprev := st240_p487
  have hstep := st240_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p489 : ((9852734183769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT240 (i+1))
      = (∑ i ∈ Finset.range 488, stT240 (i+1)) + stT240 489 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 488
    simpa using h
  have hprev := st240_p488
  have hstep := st240_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p490 : ((1940585969369/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT240 (i+1))
      = (∑ i ∈ Finset.range 489, stT240 (i+1)) + stT240 490 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 489
    simpa using h
  have hprev := st240_p489
  have hstep := st240_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p491 : ((9770954143321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT240 (i+1))
      = (∑ i ∈ Finset.range 490, stT240 (i+1)) + stT240 491 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 490
    simpa using h
  have hprev := st240_p490
  have hstep := st240_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p492 : ((2008009227581/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT240 (i+1))
      = (∑ i ∈ Finset.range 491, stT240 (i+1)) + stT240 492 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 491
    simpa using h
  have hprev := st240_p491
  have hstep := st240_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p493 : ((5223382020951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT240 (i+1))
      = (∑ i ∈ Finset.range 492, stT240 (i+1)) + stT240 493 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 492
    simpa using h
  have hprev := st240_p492
  have hstep := st240_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p494 : ((10896256267189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT240 (i+1))
      = (∑ i ∈ Finset.range 493, stT240 (i+1)) + stT240 494 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 493
    simpa using h
  have hprev := st240_p493
  have hstep := st240_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p495 : ((11284528819687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT240 (i+1))
      = (∑ i ∈ Finset.range 494, stT240 (i+1)) + stT240 495 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 494
    simpa using h
  have hprev := st240_p494
  have hstep := st240_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p496 : ((11522483259037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT240 (i+1))
      = (∑ i ∈ Finset.range 495, stT240 (i+1)) + stT240 496 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 495
    simpa using h
  have hprev := st240_p495
  have hstep := st240_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p497 : ((11556168395893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT240 (i+1))
      = (∑ i ∈ Finset.range 496, stT240 (i+1)) + stT240 497 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 496
    simpa using h
  have hprev := st240_p496
  have hstep := st240_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p498 : ((11378683279679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT240 (i+1))
      = (∑ i ∈ Finset.range 497, stT240 (i+1)) + stT240 498 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 497
    simpa using h
  have hprev := st240_p497
  have hstep := st240_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p499 : ((11031183861531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT240 (i+1))
      = (∑ i ∈ Finset.range 498, stT240 (i+1)) + stT240 499 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 498
    simpa using h
  have hprev := st240_p498
  have hstep := st240_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_p500 : ((423720519033/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT240 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT240 (i+1))
      = (∑ i ∈ Finset.range 499, stT240 (i+1)) + stT240 500 := by
    have h := Finset.sum_range_succ (fun i => stT240 (i+1)) 499
    simpa using h
  have hprev := st240_p499
  have hstep := st240_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st240_s500 :
    |Real.sin (((240 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))
      - ((200329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 1837437/2500000) (δ := 12003/1000000000) (ψ := -109777/200000) 240 237
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 240`** (evaluated boundary). -/
theorem station_240_sign : hardyG ((((240:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 240 500 (by norm_num) (by norm_num)
    ((-109777/200000 : ℚ) : ℝ)
  have hchain := st240_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT240 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((240 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-109777/200000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st240_c500
  have hsinb := abs_le.mp st240_s500
  have hbdy_lo : ((-21287887503287/1152005000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((240 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-109777/200000 : ℚ) : ℝ))) / 2
          - ((((240:ℕ)):ℝ))
            * Real.sin (((240 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-109777/200000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((240:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((240:ℝ) * Real.log (500:ℝ) - ((-109777/200000 : ℚ) : ℝ))) / 2
        - ((240:ℝ)) * Real.sin ((240:ℝ) * Real.log (500:ℝ) - ((-109777/200000 : ℚ) : ℝ))
        ≥ ((-95202241/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((240:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-95202241/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (223607/5000000)
          * ((-95202241/2000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((-95202241/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((240:ℕ)):ℝ))+1) * (((((240:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((6875576038181/15000000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((423720519033/400000000000 : ℚ) : ℝ) + ((-21287887503287/1152005000000000 : ℚ) : ℝ)
      - ((6875576038181/15000000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-109777/200000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((240:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-109777/200000 : ℚ) : ℝ)
        * (riemannZeta (line ((((240:ℕ)):ℝ)))).re
      - Real.sin ((-109777/200000 : ℚ) : ℝ)
        * (riemannZeta (line ((((240:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((240:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((240:ℕ)):ℝ))
      = (((((240:ℕ)):ℝ)) * (Real.log ((((240:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((240:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_240
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
  have hθwin : |(((-109777/200000 : ℚ) : ℝ) + ((51:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((240:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((240:ℕ)):ℝ)))
    (φ := ((-109777/200000 : ℚ) : ℝ) + ((51:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-109777/200000 : ℚ) : ℝ) + ((51:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-109777/200000 : ℚ)) : ℝ) - Real.pi) + ((51:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-109777/200000 : ℚ)) : ℝ) - Real.pi) 51).1,
    (cos_sin_shift ((((-109777/200000 : ℚ)) : ℝ) - Real.pi) 51).2]
  exact cos_sin_flip ((-109777/200000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_240_sign
end AxiomAudit
