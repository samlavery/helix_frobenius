import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 235` (rung-235.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT235 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((235 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))

theorem st235_c1 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((30597/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15999/312500) (δ := 201/1000000000) (ψ := -204787/1000000) 235 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t1 : ((489527/500000 : ℚ) : ℝ) ≤ stT235 1 := by
  have hc : ((489527/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((489527/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((489527/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c2 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((964183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -671127/10000000) (δ := 2363/200000000) (ψ := -204787/1000000) 235 26
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t2 : ((6817449039911/10000000000000 : ℚ) : ℝ) ≤ stT235 2 := by
  have hc : ((964133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6817449039911/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((964133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c3 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((359627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 192017/1000000) (δ := 11907/1000000000) (ψ := -204787/1000000) 235 41
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t3 : ((519040716551/1250000000000 : ℚ) : ℝ) ≤ stT235 3 := by
  have hc : ((179801/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((519040716551/1250000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((179801/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c4 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((737337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115887/625000) (δ := 2957/250000000) (ψ := -204787/1000000) 235 52
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t4 : ((737287/2000000 : ℚ) : ℝ) ≤ stT235 4 := by
  have hc : ((737287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((737287/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((737287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c5 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((3469/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3578967/10000000) (δ := 11771/1000000000) (ψ := -204787/1000000) 235 60
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t5 : ((12406596917/200000000000 : ℚ) : ℝ) ≤ stT235 5 := by
  have hc : ((13871/100000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12406596917/200000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((13871/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c6 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((59803/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 147421/2000000) (δ := 149/12500000) (ψ := -204787/1000000) 235 67
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t6 : ((976527653159/2500000000000 : ℚ) : ℝ) ≤ stT235 6 := by
  have hc : ((478399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((976527653159/2500000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((478399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c7 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((381983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1473569/5000000) (δ := 11777/1000000000) (ψ := -204787/1000000) 235 73
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t7 : ((360892692963/2500000000000 : ℚ) : ℝ) ≤ stT235 7 := by
  have hc : ((381933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((360892692963/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((381933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c8 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((87107/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3037257/10000000) (δ := 11841/1000000000) (ψ := -204787/1000000) 235 78
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t8 : ((615850957737/5000000000000 : ℚ) : ℝ) ≤ stT235 8 := by
  have hc : ((174189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((615850957737/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((174189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c9 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((118577/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3328403/10000000) (δ := 1189/100000000) (ψ := -204787/1000000) 235 82
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t9 : ((49396661727/625000000000 : ℚ) : ℝ) ≤ stT235 9 := by
  have hc : ((14819/62500 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49396661727/625000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((14819/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c10 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((574881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2395843/10000000) (δ := 2971/250000000) (ψ := -204787/1000000) 235 86
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t10 : ((1817774850187/10000000000000 : ℚ) : ℝ) ≤ stT235 10 := by
  have hc : ((574831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1817774850187/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((574831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c11 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-204263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4441267/10000000) (δ := 1481/125000000) (ψ := -204787/1000000) 235 90
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t11 : ((-308013493341/5000000000000 : ℚ) : ℝ) ≤ stT235 11 := by
  have hc : ((-204313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-308013493341/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-204313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c12 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((246033/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11149/250000) (δ := 5967/500000000) (ψ := -204787/1000000) 235 93
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t12 : ((1420399848791/5000000000000 : ℚ) : ℝ) ≤ stT235 12 := by
  have hc : ((492041/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1420399848791/5000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((492041/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c13 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((30511/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -544763/10000000) (δ := 11791/1000000000) (ψ := -204787/1000000) 235 96
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t13 : ((2707773597/10000000000 : ℚ) : ℝ) ≤ stT235 13 := by
  have hc : ((488151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2707773597/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((488151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c14 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-16239/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4130203/10000000) (δ := 11791/1000000000) (ψ := -204787/1000000) 235 99
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t14 : ((-43427288637/2000000000000 : ℚ) : ℝ) ≤ stT235 14 := by
  have hc : ((-16249/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43427288637/2000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-16249/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c15 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-82297/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4987199/10000000) (δ := 2969/250000000) (ψ := -204787/1000000) 235 101
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t15 : ((-212515768623/2000000000000 : ℚ) : ℝ) ≤ stT235 15 := by
  have hc : ((-82307/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-212515768623/2000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-82307/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c16 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-117063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2110161/5000000) (δ := 2371/200000000) (ψ := -204787/1000000) 235 104
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t16 : ((-292782617113/10000000000000 : ℚ) : ℝ) ≤ stT235 16 := by
  have hc : ((-117113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-292782617113/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-117113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c17 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((99997/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -603/312500) (δ := 37/3125000) (ψ := -204787/1000000) 235 106
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t17 : ((7578631161/31250000000 : ℚ) : ℝ) ≤ stT235 17 := by
  have hc : ((12499/12500 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7578631161/31250000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((12499/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c18 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((13077/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1072669/5000000) (δ := 11877/1000000000) (ψ := -204787/1000000) 235 108
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t18 : ((3852552459/25000000000 : ℚ) : ℝ) ≤ stT235 18 := by
  have hc : ((3269/5000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3852552459/25000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((3269/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c19 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((542357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2493891/10000000) (δ := 2953/250000000) (ψ := -204787/1000000) 235 110
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t19 : ((1244137400199/10000000000000 : ℚ) : ℝ) ≤ stT235 19 := by
  have hc : ((542307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1244137400199/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((542307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c20 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((884623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 606389/5000000) (δ := 11897/1000000000) (ψ := -204787/1000000) 235 112
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t20 : ((1977964494391/10000000000000 : ℚ) : ℝ) ≤ stT235 20 := by
  have hc : ((884573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1977964494391/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((884573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c21 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((816449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -769453/5000000) (δ := 11883/1000000000) (ψ := -204787/1000000) 235 114
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t21 : ((890763968511/5000000000000 : ℚ) : ℝ) ≤ stT235 21 := by
  have hc : ((816399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((890763968511/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((816399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c22 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-313983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1406083/2500000) (δ := 5917/500000000) (ψ := -204787/1000000) 235 116
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t22 : ((-10460430751/78125000000 : ℚ) : ℝ) ≤ stT235 22 := by
  have hc : ((-39251/62500 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10460430751/78125000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-39251/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c23 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-83951/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4783137/10000000) (δ := 11761/1000000000) (ψ := -204787/1000000) 235 117
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t23 : ((-70030428883/1000000000000 : ℚ) : ℝ) ≤ stT235 23 := by
  have hc : ((-167927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70030428883/1000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-167927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c24 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((198777/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65161/400000) (δ := 11947/1000000000) (ψ := -204787/1000000) 235 119
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t24 : ((811452493489/5000000000000 : ℚ) : ℝ) ≤ stT235 24 := by
  have hc : ((397529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((811452493489/5000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((397529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c25 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-13836/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6645937/10000000) (δ := 37/3125000) (ψ := -204787/1000000) 235 120
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t25 : ((-885554442777/5000000000000 : ℚ) : ℝ) ≤ stT235 25 := by
  have hc : ((-442777/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-885554442777/5000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-442777/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c26 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((30821/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -431957/2500000) (δ := 11777/1000000000) (ψ := -204787/1000000) 235 122
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t26 : ((60441020859/400000000000 : ℚ) : ℝ) ≤ stT235 26 := by
  have hc : ((30819/40000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60441020859/400000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((30819/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c27 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-159113/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 947327/2000000) (δ := 2357/200000000) (ψ := -204787/1000000) 235 123
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t27 : ((-153130620069/2500000000000 : ℚ) : ℝ) ≤ stT235 27 := by
  have hc : ((-79569/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153130620069/2500000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-79569/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c28 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-8227/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1328317/2500000) (δ := 2951/250000000) (ψ := -204787/1000000) 235 125
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t28 : ((-497569607847/5000000000000 : ℚ) : ℝ) ≤ stT235 28 := by
  have hc : ((-263289/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-497569607847/5000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-263289/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c29 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((986901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -101273/2500000) (δ := 5953/500000000) (ψ := -204787/1000000) 235 126
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t29 : ((1832535925003/10000000000000 : ℚ) : ℝ) ≤ stT235 29 := by
  have hc : ((986851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1832535925003/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((986851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c30 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((24573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 951019/2500000) (δ := 11913/1000000000) (ψ := -204787/1000000) 235 127
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t30 : ((11204572517/1250000000000 : ℚ) : ℝ) ≤ stT235 30 := by
  have hc : ((6137/125000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11204572517/1250000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((6137/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c31 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-245139/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7360179/10000000) (δ := 149/12500000) (ψ := -204787/1000000) 235 128
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t31 : ((-440305332181/2500000000000 : ℚ) : ℝ) ≤ stT235 31 := by
  have hc : ((-490303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-440305332181/2500000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-490303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c32 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-22273/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5403387/10000000) (δ := 2967/250000000) (ψ := -204787/1000000) 235 130
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t32 : ((-1575080397/16000000000 : ℚ) : ℝ) ≤ stT235 32 := by
  have hc : ((-891/1600 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1575080397/16000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-891/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c33 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((350011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -606607/2000000) (δ := 11761/1000000000) (ψ := -204787/1000000) 235 131
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t33 : ((76150463717/1250000000000 : ℚ) : ℝ) ≤ stT235 33 := by
  have hc : ((349961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76150463717/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((349961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c34 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((443279/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1202361/10000000) (δ := 5927/500000000) (ψ := -204787/1000000) 235 132
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t34 : ((76017396119/500000000000 : ℚ) : ℝ) ≤ stT235 34 := by
  have hc : ((221627/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76017396119/500000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((221627/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c35 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((998851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14979/1250000) (δ := 11847/1000000000) (ψ := -204787/1000000) 235 133
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t35 : ((422070330177/2500000000000 : ℚ) : ℝ) ≤ stT235 35 := by
  have hc : ((998801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((422070330177/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((998801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c36 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((926833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 962273/10000000) (δ := 1483/125000000) (ψ := -204787/1000000) 235 134
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t36 : ((772318857739/5000000000000 : ℚ) : ℝ) ≤ stT235 36 := by
  have hc : ((926783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((772318857739/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((926783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c37 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((857457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 675611/5000000) (δ := 11771/1000000000) (ψ := -204787/1000000) 235 135
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t37 : ((1409567676523/10000000000000 : ℚ) : ℝ) ≤ stT235 37 := by
  have hc : ((857407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1409567676523/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((857407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c38 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((865659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 655413/5000000) (δ := 473/40000000) (ψ := -204787/1000000) 235 136
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t38 : ((702101519163/5000000000000 : ℚ) : ℝ) ≤ stT235 38 := by
  have hc : ((865609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((702101519163/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((865609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c39 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((58809/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 863469/10000000) (δ := 5909/500000000) (ψ := -204787/1000000) 235 137
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t39 : ((753317842607/5000000000000 : ℚ) : ℝ) ≤ stT235 39 := by
  have hc : ((470447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((753317842607/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((470447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c40 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((999929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29713/10000000) (δ := 11911/1000000000) (ψ := -204787/1000000) 235 138
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t40 : ((790473341151/5000000000000 : ℚ) : ℝ) ≤ stT235 40 := by
  have hc : ((999879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((790473341151/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((999879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c41 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((892229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1171347/10000000) (δ := 11899/1000000000) (ψ := -204787/1000000) 235 139
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t41 : ((1393348954923/10000000000000 : ℚ) : ℝ) ≤ stT235 41 := by
  have hc : ((892179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1393348954923/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((892179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c42 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((463559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2721971/10000000) (δ := 1487/125000000) (ψ := -204787/1000000) 235 140
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t42 : ((715209682797/10000000000000 : ℚ) : ℝ) ≤ stT235 42 := by
  have hc : ((463509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((715209682797/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((463509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c43 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-134093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -921153/2000000) (δ := 5907/500000000) (ψ := -204787/1000000) 235 141
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t43 : ((-51132018087/1250000000000 : ℚ) : ℝ) ≤ stT235 43 := by
  have hc : ((-67059/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51132018087/1250000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-67059/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c44 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-182729/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6807397/10000000) (δ := 11821/1000000000) (ψ := -204787/1000000) 235 142
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t44 : ((-275489458623/2000000000000 : ℚ) : ℝ) ≤ stT235 44 := by
  have hc : ((-182739/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275489458623/2000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-182739/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c45 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-834571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6395373/10000000) (δ := 11821/1000000000) (ψ := -204787/1000000) 235 142
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t45 : ((-155522442519/1250000000000 : ℚ) : ℝ) ≤ stT235 45 := by
  have hc : ((-834621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155522442519/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-834621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c46 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((130419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3600013/10000000) (δ := 19/1600000) (ψ := -204787/1000000) 235 143
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t46 : ((192218530611/10000000000000 : ℚ) : ℝ) ≤ stT235 46 := by
  have hc : ((130369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192218530611/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((130369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c47 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((122233/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 527001/10000000) (δ := 2967/250000000) (ψ := -204787/1000000) 235 144
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t47 : ((713143706643/5000000000000 : ℚ) : ℝ) ≤ stT235 47 := by
  have hc : ((488907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((713143706643/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((488907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c48 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((17253/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2812089/10000000) (δ := 11943/1000000000) (ψ := -204787/1000000) 235 145
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t48 : ((199197297/3200000000 : ℚ) : ℝ) ≤ stT235 48 := by
  have hc : ((17251/40000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199197297/3200000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((17251/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c49 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-167393/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6406273/10000000) (δ := 11853/1000000000) (ψ := -204787/1000000) 235 146
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t49 : ((-59786809629/500000000000 : ℚ) : ℝ) ≤ stT235 49 := by
  have hc : ((-167403/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59786809629/500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-167403/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c50 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-57643/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 682859/1250000) (δ := 11853/1000000000) (ψ := -204787/1000000) 235 146
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t50 : ((-2547706521/31250000000 : ℚ) : ℝ) ≤ stT235 50 := by
  have hc : ((-3603/6250 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2547706521/31250000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-3603/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c51 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((424799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 173617/1250000) (δ := 5973/500000000) (ψ := -204787/1000000) 235 147
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t51 : ((7435031709/62500000000 : ℚ) : ℝ) ≤ stT235 51 := by
  have hc : ((212387/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7435031709/62500000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((212387/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c52 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((395341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2910893/10000000) (δ := 2941/250000000) (ψ := -204787/1000000) 235 148
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t52 : ((2192679177/40000000000 : ℚ) : ℝ) ≤ stT235 52 := by
  have hc : ((395291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2192679177/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((395291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c53 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-985521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7428039/10000000) (δ := 1479/125000000) (ψ := -204787/1000000) 235 149
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t53 : ((-676893119513/5000000000000 : ℚ) : ℝ) ≤ stT235 53 := by
  have hc : ((-985571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-676893119513/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-985571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c54 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((74407/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 355357/1000000) (δ := 11771/1000000000) (ψ := -204787/1000000) 235 149
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t54 : ((50610516957/2500000000000 : ℚ) : ℝ) ≤ stT235 54 := by
  have hc : ((37191/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50610516957/2500000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((37191/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c55 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((852671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1374297/10000000) (δ := 5889/500000000) (ψ := -204787/1000000) 235 150
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t55 : ((1149673303779/10000000000000 : ℚ) : ℝ) ≤ stT235 55 := by
  have hc : ((852621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1149673303779/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((852621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c56 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-53509/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -812049/1250000) (δ := 11917/1000000000) (ψ := -204787/1000000) 235 151
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t56 : ((-572069017779/5000000000000 : ℚ) : ℝ) ≤ stT235 56 := by
  have hc : ((-428097/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-572069017779/5000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-428097/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c57 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((9947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3902123/10000000) (δ := 11917/1000000000) (ψ := -204787/1000000) 235 151
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t57 : ((3277223301/2500000000000 : ℚ) : ℝ) ≤ stT235 57 := by
  have hc : ((9897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3277223301/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((9897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c58 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((201229/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1588157/10000000) (δ := 11893/1000000000) (ψ := -204787/1000000) 235 152
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t58 : ((66052535589/625000000000 : ℚ) : ℝ) ≤ stT235 58 := by
  have hc : ((402433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66052535589/625000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((402433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c59 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-48563/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7253161/10000000) (δ := 11903/1000000000) (ψ := -204787/1000000) 235 153
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t59 : ((-12645387759/100000000000 : ℚ) : ℝ) ≤ stT235 59 := by
  have hc : ((-97131/100000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12645387759/100000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-97131/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c60 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((249477/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2621011/10000000) (δ := 119/10000000) (ψ := -204787/1000000) 235 153
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t60 : ((40255129411/625000000000 : ℚ) : ℝ) ≤ stT235 60 := by
  have hc : ((62363/125000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40255129411/625000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((62363/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c61 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((218621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3375989/10000000) (δ := 2949/250000000) (ψ := -204787/1000000) 235 154
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t61 : ((17490707133/625000000000 : ℚ) : ℝ) ≤ stT235 61 := by
  have hc : ((218571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17490707133/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((218571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c62 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-783343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1235411/2000000) (δ := 11807/1000000000) (ψ := -204787/1000000) 235 154
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t62 : ((-497455338393/5000000000000 : ℚ) : ℝ) ≤ stT235 62 := by
  have hc : ((-783393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-497455338393/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-783393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c63 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((499317/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -130673/10000000) (δ := 5957/500000000) (ψ := -204787/1000000) 235 155
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t63 : ((157262126063/1250000000000 : ℚ) : ℝ) ≤ stT235 63 := by
  have hc : ((124823/125000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157262126063/1250000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((124823/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c64 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-874211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -658651/1000000) (δ := 5961/500000000) (ψ := -204787/1000000) 235 156
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t64 : ((-1092827124261/10000000000000 : ℚ) : ℝ) ≤ stT235 64 := by
  have hc : ((-874261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1092827124261/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-874261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c65 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((266403/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2522207/10000000) (δ := 11781/1000000000) (ψ := -204787/1000000) 235 156
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t65 : ((165200576583/2500000000000 : ℚ) : ℝ) ≤ stT235 65 := by
  have hc : ((133189/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165200576583/2500000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((133189/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c66 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-57693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42161/100000) (δ := 5887/500000000) (ψ := -204787/1000000) 235 157
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t66 : ((-7104595197/500000000000 : ℚ) : ℝ) ≤ stT235 66 := by
  have hc : ((-28859/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7104595197/500000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-28859/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c67 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-136577/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2309333/5000000) (δ := 5937/500000000) (ψ := -204787/1000000) 235 157
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t67 : ((-16688598039/500000000000 : ℚ) : ℝ) ≤ stT235 67 := by
  have hc : ((-68301/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16688598039/500000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-68301/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c68 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((289143/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1192713/5000000) (δ := 11867/1000000000) (ψ := -204787/1000000) 235 158
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t68 : ((87651759501/1250000000000 : ℚ) : ℝ) ≤ stT235 68 := by
  have hc : ((144559/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87651759501/1250000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((144559/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c69 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-786889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6191369/10000000) (δ := 11867/1000000000) (ψ := -204787/1000000) 235 158
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t69 : ((-947363597601/10000000000000 : ℚ) : ℝ) ≤ stT235 69 := by
  have hc : ((-786939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-947363597601/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-786939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c70 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((455459/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1063233/10000000) (δ := 593/50000000) (ψ := -204787/1000000) 235 159
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t70 : ((68043433619/625000000000 : ℚ) : ℝ) ≤ stT235 70 := by
  have hc : ((227717/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68043433619/625000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((227717/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c71 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-972861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 363511/500000) (δ := 11843/1000000000) (ψ := -204787/1000000) 235 159
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t71 : ((-577316631201/5000000000000 : ℚ) : ℝ) ≤ stT235 71 := by
  have hc : ((-972911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-577316631201/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-972911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c72 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((996103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -27599/1250000) (δ := 237/20000000) (ψ := -204787/1000000) 235 160
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t72 : ((1173859417083/10000000000000 : ℚ) : ℝ) ≤ stT235 72 := by
  have hc : ((996053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1173859417083/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((996053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c73 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-499967/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -978149/1250000) (δ := 5923/500000000) (ψ := -204787/1000000) 235 161
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t73 : ((-18287394897/156250000000 : ℚ) : ℝ) ≤ stT235 73 := by
  have hc : ((-62499/62500 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18287394897/156250000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-62499/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c74 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((49887/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 84049/5000000) (δ := 5923/500000000) (ψ := -204787/1000000) 235 161
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t74 : ((28994767011/250000000000 : ℚ) : ℝ) ≤ stT235 74 := by
  have hc : ((99769/100000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28994767011/250000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((99769/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c75 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-249199/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3826897/5000000) (δ := 5919/500000000) (ψ := -204787/1000000) 235 162
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t75 : ((-575529536523/5000000000000 : ℚ) : ℝ) ≤ stT235 75 := by
  have hc : ((-498423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-575529536523/5000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-498423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c76 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((499347/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 127761/10000000) (δ := 5919/500000000) (ψ := -204787/1000000) 235 162
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t76 : ((143190320279/1250000000000 : ℚ) : ℝ) ≤ stT235 76 := by
  have hc : ((249661/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143190320279/1250000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((249661/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c77 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-249957/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 390381/500000) (δ := 2353/200000000) (ψ := -204787/1000000) 235 162
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t77 : ((-284866742017/2500000000000 : ℚ) : ℝ) ≤ stT235 77 := by
  have hc : ((-499939/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284866742017/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-499939/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c78 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((6199/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -79899/2500000) (δ := 11831/1000000000) (ψ := -204787/1000000) 235 163
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t78 : ((112298100583/1000000000000 : ℚ) : ℝ) ≤ stT235 78 := by
  have hc : ((99179/100000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112298100583/1000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((99179/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c79 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-962217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7164567/10000000) (δ := 371/31250000) (ψ := -204787/1000000) 235 163
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t79 : ((-33832345453/312500000000 : ℚ) : ℝ) ≤ stT235 79 := by
  have hc : ((-962267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33832345453/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-962267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c80 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((27983/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -144169/1250000) (δ := 2981/250000000) (ψ := -204787/1000000) 235 164
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t80 : ((500546728199/5000000000000 : ℚ) : ℝ) ≤ stT235 80 := by
  have hc : ((447703/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((500546728199/5000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((447703/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c81 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-31011/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6144867/10000000) (δ := 739/62500000) (ψ := -204787/1000000) 235 164
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t81 : ((-4307364557/50000000000 : ℚ) : ℝ) ≤ stT235 81 := by
  have hc : ((-31013/40000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4307364557/50000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-31013/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c82 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((294181/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -588603/2500000) (δ := 5943/500000000) (ψ := -204787/1000000) 235 165
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t82 : ((16242044157/250000000000 : ℚ) : ℝ) ≤ stT235 82 := by
  have hc : ((73539/125000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16242044157/250000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((73539/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c83 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-329683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 476691/1000000) (δ := 11817/1000000000) (ψ := -204787/1000000) 235 165
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t83 : ((-361929119319/10000000000000 : ℚ) : ℝ) ≤ stT235 83 := by
  have hc : ((-329733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-361929119319/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-329733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c84 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((877/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -781013/2000000) (δ := 2351/100000000) (ψ := -204787/1000000) 235 166
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t84 : ((118928701/125000000000 : ℚ) : ℝ) ≤ stT235 84 := by
  have hc : ((109/12500 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118928701/125000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((109/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c85 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((344519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1523837/5000000) (δ := 1191/100000000) (ψ := -204787/1000000) 235 166
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t85 : ((93407247447/2500000000000 : ℚ) : ℝ) ≤ stT235 85 := by
  have hc : ((344469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93407247447/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((344469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c86 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-135559/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5788889/10000000) (δ := 11803/1000000000) (ψ := -204787/1000000) 235 167
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t86 : ((-18273481079/250000000000 : ℚ) : ℝ) ≤ stT235 86 := by
  have hc : ((-135569/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18273481079/250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-135569/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c87 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((920571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50157/500000) (δ := 59/5000000) (ψ := -204787/1000000) 235 167
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t87 : ((61681350647/625000000000 : ℚ) : ℝ) ≤ stT235 87 := by
  have hc : ((920521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61681350647/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((920521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c88 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-99851/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7717501/10000000) (δ := 11803/1000000000) (ψ := -204787/1000000) 235 167
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t88 : ((-1663232741/15625000000 : ℚ) : ℝ) ≤ stT235 88 := by
  have hc : ((-6241/6250 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1663232741/15625000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-6241/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c89 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((53581/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -676003/5000000) (δ := 2359/200000000) (ψ := -204787/1000000) 235 168
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t89 : ((454339094131/5000000000000 : ℚ) : ℝ) ≤ stT235 89 := by
  have hc : ((428623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454339094131/5000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((428623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c90 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-19671/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1303077/2500000) (δ := 369/31250000) (ψ := -204787/1000000) 235 168
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t90 : ((-20737171589/400000000000 : ℚ) : ℝ) ≤ stT235 90 := by
  have hc : ((-19673/40000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20737171589/400000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-19673/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c91 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-15373/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4003869/10000000) (δ := 2961/125000000) (ψ := -204787/1000000) 235 169
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t91 : ((-1614149243/500000000000 : ℚ) : ℝ) ≤ stT235 91 := by
  have hc : ((-7699/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1614149243/500000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-7699/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c92 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((567953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 604237/2500000) (δ := 743/62500000) (ψ := -204787/1000000) 235 169
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t92 : ((148019941629/2500000000000 : ℚ) : ℝ) ≤ stT235 92 := by
  have hc : ((567903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148019941629/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((567903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c93 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-29183/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6939611/10000000) (δ := 5911/500000000) (ψ := -204787/1000000) 235 170
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t93 : ((-60525980907/625000000000 : ℚ) : ℝ) ≤ stT235 93 := by
  have hc : ((-466953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60525980907/625000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-466953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c94 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((482879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -328061/5000000) (δ := 5961/500000000) (ψ := -204787/1000000) 235 170
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t94 : ((249012877767/2500000000000 : ℚ) : ℝ) ≤ stT235 94 := by
  have hc : ((241427/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249012877767/2500000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((241427/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c95 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-608007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5560861/10000000) (δ := 11881/1000000000) (ψ := -204787/1000000) 235 170
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t95 : ((-623853712803/10000000000000 : ℚ) : ℝ) ≤ stT235 95 := by
  have hc : ((-608057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-623853712803/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-608057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c96 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-5457/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3995213/10000000) (δ := 11829/1000000000) (ψ := -204787/1000000) 235 171
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t96 : ((-5579735007/2000000000000 : ℚ) : ℝ) ≤ stT235 96 := by
  have hc : ((-5467/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5579735007/2000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-5467/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c97 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((133913/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 523233/2500000) (δ := 11829/1000000000) (ψ := -204787/1000000) 235 171
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t97 : ((67978937719/1000000000000 : ℚ) : ℝ) ≤ stT235 97 := by
  have hc : ((133903/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67978937719/1000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((133903/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c98 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-497201/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3794669/5000000) (δ := 11867/1000000000) (ψ := -204787/1000000) 235 172
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t98 : ((-251137167789/2500000000000 : ℚ) : ℝ) ≤ stT235 98 := by
  have hc : ((-248613/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251137167789/2500000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-248613/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c99 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((796131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1624803/10000000) (δ := 11867/1000000000) (ψ := -204787/1000000) 235 172
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t99 : ((800090859997/10000000000000 : ℚ) : ℝ) ≤ stT235 99 := by
  have hc : ((796081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((800090859997/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((796081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c100 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-35159/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4279749/10000000) (δ := 373/31250000) (ψ := -204787/1000000) 235 172
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t100 : ((-70343/5000000 : ℚ) : ℝ) ≤ stT235 100 := by
  have hc : ((-70343/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70343/5000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-70343/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c101 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-614811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1116471/2000000) (δ := 11859/1000000000) (ψ := -204787/1000000) 235 173
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t101 : ((-305905029859/5000000000000 : ℚ) : ℝ) ≤ stT235 101 := by
  have hc : ((-614861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-305905029859/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-614861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c102 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((996611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12867/625000) (δ := 1493/125000000) (ψ := -204787/1000000) 235 173
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t102 : ((986741884467/10000000000000 : ℚ) : ℝ) ≤ stT235 102 := by
  have hc : ((996561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((986741884467/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((996561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c103 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-720301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 296879/500000) (δ := 11859/1000000000) (ψ := -204787/1000000) 235 173
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t103 : ((-70978345083/1000000000000 : ℚ) : ℝ) ≤ stT235 103 := by
  have hc : ((-720351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70978345083/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-720351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c104 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-66761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4094017/10000000) (δ := 2963/250000000) (ψ := -204787/1000000) 235 174
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t104 : ((-65513597191/10000000000000 : ℚ) : ℝ) ≤ stT235 104 := by
  have hc : ((-66811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65513597191/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-66811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c105 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((163789/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 305613/2000000) (δ := 11951/1000000000) (ψ := -204787/1000000) 235 174
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t105 : ((1598319261/20000000000 : ℚ) : ℝ) ≤ stT235 105 := by
  have hc : ((163779/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1598319261/20000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((163779/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c106 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-238621/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7096801/10000000) (δ := 11851/1000000000) (ψ := -204787/1000000) 235 174
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t106 : ((-231781377681/2500000000000 : ℚ) : ℝ) ≤ stT235 106 := by
  have hc : ((-477267/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-231781377681/2500000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-477267/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c107 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((163409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -618931/2000000) (δ := 5879/500000000) (ψ := -204787/1000000) 235 175
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t107 : ((1233978083/39062500000 : ℚ) : ℝ) ≤ stT235 107 := by
  have hc : ((20423/62500 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1233978083/39062500000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((20423/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c108 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((116629/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 474101/2000000) (δ := 5879/500000000) (ψ := -204787/1000000) 235 175
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t108 : ((448866531/8000000000 : ℚ) : ℝ) ≤ stT235 108 := by
  have hc : ((116619/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((448866531/8000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((116619/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c109 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-499811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7785257/10000000) (δ := 2389/200000000) (ψ := -204787/1000000) 235 175
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t109 : ((-119689104093/1250000000000 : ℚ) : ℝ) ≤ stT235 109 := by
  have hc : ((-124959/125000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119689104093/1250000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-124959/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c110 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((260427/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1278681/5000000) (δ := 2353/200000000) (ψ := -204787/1000000) 235 176
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t110 : ((62070852931/1250000000000 : ℚ) : ℝ) ≤ stT235 110 := by
  have hc : ((130201/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62070852931/1250000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((130201/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c111 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((450223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1379727/5000000) (δ := 5919/500000000) (ψ := -204787/1000000) 235 176
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t111 : ((427284854161/10000000000000 : ℚ) : ℝ) ≤ stT235 111 := by
  have hc : ((450173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((427284854161/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((450173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c112 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-249391/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7679457/10000000) (δ := 11931/1000000000) (ψ := -204787/1000000) 235 177
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t112 : ((-29458044999/312500000000 : ℚ) : ℝ) ≤ stT235 112 := by
  have hc : ((-498807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29458044999/312500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-498807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c113 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((554639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2457169/10000000) (δ := 2943/250000000) (ψ := -204787/1000000) 235 177
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t113 : ((6521412051/125000000000 : ℚ) : ℝ) ≤ stT235 113 := by
  have hc : ((554589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6521412051/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((554589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c114 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((464591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1359529/5000000) (δ := 11931/1000000000) (ψ := -204787/1000000) 235 177
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t114 : ((87016426497/2000000000000 : ℚ) : ℝ) ≤ stT235 114 := by
  have hc : ((464541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87016426497/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((464541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c115 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-999999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7850107/10000000) (δ := 11831/1000000000) (ψ := -204787/1000000) 235 177
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t115 : ((-186510138549/2000000000000 : ℚ) : ℝ) ≤ stT235 115 := by
  have hc : ((-1000049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-186510138549/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-1000049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c116 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((445993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2771281/10000000) (δ := 11779/1000000000) (ψ := -204787/1000000) 235 178
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t116 : ((103511843217/2500000000000 : ℚ) : ℝ) ≤ stT235 116 := by
  have hc : ((445943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103511843217/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((445943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c117 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((614787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2271701/10000000) (δ := 2981/250000000) (ψ := -204787/1000000) 235 178
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t117 : ((1136648713/20000000000 : ℚ) : ℝ) ≤ stT235 117 := by
  have hc : ((614737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1136648713/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((614737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c118 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-486501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3635869/5000000) (δ := 11879/1000000000) (ψ := -204787/1000000) 235 178
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t118 : ((-8957673449/100000000000 : ℚ) : ℝ) ≤ stT235 118 := by
  have hc : ((-243263/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8957673449/100000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-243263/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c119 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((178463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3478431/10000000) (δ := 2979/250000000) (ψ := -204787/1000000) 235 179
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t119 : ((81775420137/5000000000000 : ℚ) : ℝ) ≤ stT235 119 := by
  have hc : ((178413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81775420137/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((178413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c120 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((167819/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 718973/5000000) (δ := 11887/1000000000) (ψ := -204787/1000000) 235 179
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t120 : ((15318780183/200000000000 : ℚ) : ℝ) ≤ stT235 120 := by
  have hc : ((167809/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15318780183/200000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((167809/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c121 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-816083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6313491/10000000) (δ := 11887/1000000000) (ψ := -204787/1000000) 235 179
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t121 : ((-741939165103/10000000000000 : ℚ) : ℝ) ≤ stT235 121 := by
  have hc : ((-816133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-741939165103/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-816133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c122 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-12507/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2279527/5000000) (δ := 11809/1000000000) (ψ := -204787/1000000) 235 180
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t122 : ((-11325575901/500000000000 : ℚ) : ℝ) ≤ stT235 122 := by
  have hc : ((-25019/100000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11325575901/500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-25019/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c123 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((497757/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47377/2000000) (δ := 5897/500000000) (ψ := -204787/1000000) 235 180
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t123 : ((112197378677/1250000000000 : ℚ) : ℝ) ≤ stT235 123 := by
  have hc : ((124433/125000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112197378677/1250000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((124433/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c124 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-10349/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 499399/1000000) (δ := 5897/500000000) (ψ := -204787/1000000) 235 180
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t124 : ((-37179215827/1000000000000 : ℚ) : ℝ) ≤ stT235 124 := by
  have hc : ((-41401/100000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37179215827/1000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-41401/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c125 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-92007/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -374691/625000) (δ := 5901/500000000) (ψ := -204787/1000000) 235 181
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t125 : ((-82299227171/1250000000000 : ℚ) : ℝ) ≤ stT235 125 := by
  have hc : ((-368053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82299227171/1250000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-368053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c126 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((216269/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -656869/5000000) (δ := 11901/1000000000) (ψ := -204787/1000000) 235 181
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t126 : ((38531285631/500000000000 : ℚ) : ℝ) ≤ stT235 126 := by
  have hc : ((432513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38531285631/500000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((432513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c127 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((14771/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 832627/2500000) (δ := 11801/1000000000) (ψ := -204787/1000000) 235 181
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t127 : ((26208724977/1250000000000 : ℚ) : ℝ) ≤ stT235 127 := by
  have hc : ((118143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26208724977/1250000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((118143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c128 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-99943/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -310783/400000) (δ := 2977/250000000) (ψ := -204787/1000000) 235 182
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t128 : ((-5521402377/62500000000 : ℚ) : ℝ) ≤ stT235 128 := by
  have hc : ((-24987/25000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5521402377/62500000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-24987/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c129 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((14383/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3197533/10000000) (δ := 2359/200000000) (ψ := -204787/1000000) 235 182
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t129 : ((506452449/20000000000 : ℚ) : ℝ) ≤ stT235 129 := by
  have hc : ((28761/100000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((506452449/20000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((28761/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c130 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((429967/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 669571/5000000) (δ := 2359/200000000) (ψ := -204787/1000000) 235 182
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t130 : ((94271017659/1250000000000 : ℚ) : ℝ) ≤ stT235 130 := by
  have hc : ((214971/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94271017659/1250000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((214971/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c131 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-693/1000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 730137/1250000) (δ := 369/31250000) (ψ := -204787/1000000) 235 182
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t131 : ((-2422085001/40000000000 : ℚ) : ℝ) ≤ stT235 131 := by
  have hc : ((-13861/20000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2422085001/40000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-13861/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c132 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-555421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1079833/2000000) (δ := 2947/250000000) (ψ := -204787/1000000) 235 183
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t132 : ((-483475848219/10000000000000 : ℚ) : ℝ) ≤ stT235 132 := by
  have hc : ((-555471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-483475848219/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-555471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c133 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((185279/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -193037/2000000) (δ := 2947/250000000) (ψ := -204787/1000000) 235 183
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t133 : ((160648417321/2000000000000 : ℚ) : ℝ) ≤ stT235 133 := by
  have hc : ((185269/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160648417321/2000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((185269/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c134 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((24413/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 858893/2500000) (δ := 4703/200000000) (ψ := -204787/1000000) 235 183
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t134 : ((21084210309/1250000000000 : ℚ) : ℝ) ≤ stT235 134 := by
  have hc : ((97627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21084210309/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((97627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c135 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-999797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1560721/2000000) (δ := 2947/250000000) (ψ := -204787/1000000) 235 183
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t135 : ((-860531318561/10000000000000 : ℚ) : ℝ) ≤ stT235 135 := by
  have hc : ((-999847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-860531318561/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-999847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c136 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((71443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3568549/10000000) (δ := 11923/1000000000) (ψ := -204787/1000000) 235 184
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t136 : ((7655045457/625000000000 : ℚ) : ℝ) ≤ stT235 136 := by
  have hc : ((35709/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7655045457/625000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((35709/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c137 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((95703/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 367767/5000000) (δ := 297/25000000) (ψ := -204787/1000000) 235 184
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t137 : ((40880128093/500000000000 : ℚ) : ℝ) ≤ stT235 137 := by
  have hc : ((47849/50000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40880128093/500000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((47849/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c138 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-52393/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2504123/5000000) (δ := 11923/1000000000) (ψ := -204787/1000000) 235 184
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t138 : ((-178420913429/5000000000000 : ℚ) : ℝ) ≤ stT235 138 := by
  have hc : ((-209597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178420913429/5000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-209597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c139 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-13251/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6457791/10000000) (δ := 1193/100000000) (ψ := -204787/1000000) 235 185
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t139 : ((-359680482773/5000000000000 : ℚ) : ℝ) ≤ stT235 139 := by
  have hc : ((-424057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-359680482773/5000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-424057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c140 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((622769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1123149/5000000) (δ := 11873/1000000000) (ψ := -204787/1000000) 235 185
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t140 : ((263146726863/5000000000000 : ℚ) : ℝ) ≤ stT235 140 := by
  have hc : ((622719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((263146726863/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((622719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c141 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((715071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 77407/400000) (δ := 1183/100000000) (ψ := -204787/1000000) 235 185
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t141 : ((602155650171/10000000000000 : ℚ) : ℝ) ≤ stT235 141 := by
  have hc : ((715021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((602155650171/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((715021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c142 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-760489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1217431/2000000) (δ := 1183/100000000) (ψ := -204787/1000000) 235 185
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t142 : ((-319115319549/5000000000000 : ℚ) : ℝ) ≤ stT235 142 := by
  have hc : ((-760539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-319115319549/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-760539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c143 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-146961/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -343623/625000) (δ := 11937/1000000000) (ψ := -204787/1000000) 235 186
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t143 : ((-245811121121/5000000000000 : ℚ) : ℝ) ≤ stT235 143 := by
  have hc : ((-293947/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245811121121/5000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-293947/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c144 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((423211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -350979/2500000) (δ := 5883/500000000) (ψ := -204787/1000000) 235 186
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t144 : ((176327429469/2500000000000 : ℚ) : ℝ) ≤ stT235 144 := by
  have hc : ((211593/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176327429469/2500000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((211593/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c145 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((242361/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1330939/5000000) (δ := 11837/1000000000) (ψ := -204787/1000000) 235 186
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t145 : ((3144514071/78125000000 : ℚ) : ℝ) ≤ stT235 145 := by
  have hc : ((7573/15625 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3144514071/78125000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((7573/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c146 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-223823/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6699707/10000000) (δ := 11937/1000000000) (ψ := -204787/1000000) 235 186
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t146 : ((-185247602813/2500000000000 : ℚ) : ℝ) ≤ stT235 146 := by
  have hc : ((-447671/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185247602813/2500000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-447671/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c147 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-207717/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -124951/250000) (δ := 1493/125000000) (ψ := -204787/1000000) 235 187
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t147 : ((-85671450477/2500000000000 : ℚ) : ℝ) ≤ stT235 147 := by
  have hc : ((-103871/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85671450477/2500000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-103871/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c148 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((918713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1014967/10000000) (δ := 11859/1000000000) (ψ := -204787/1000000) 235 187
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t148 : ((377567737011/5000000000000 : ℚ) : ℝ) ≤ stT235 148 := by
  have hc : ((918663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((377567737011/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((918663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c149 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((192067/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2941317/10000000) (δ := 11759/1000000000) (ψ := -204787/1000000) 235 187
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t149 : ((78663379851/2500000000000 : ℚ) : ℝ) ≤ stT235 149 := by
  have hc : ((96021/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78663379851/2500000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((96021/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c150 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-461849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3435523/5000000) (δ := 2961/250000000) (ψ := -204787/1000000) 235 187
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t150 : ((-188559367689/2500000000000 : ℚ) : ℝ) ≤ stT235 150 := by
  have hc : ((-230937/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188559367689/2500000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-230937/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c151 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-39171/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -986643/2000000) (δ := 1469/125000000) (ψ := -204787/1000000) 235 188
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t151 : ((-3985124733/125000000000 : ℚ) : ℝ) ≤ stT235 151 := by
  have hc : ((-4897/12500 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3985124733/125000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-4897/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c152 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((456111/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -131913/1250000) (δ := 2963/250000000) (ψ := -204787/1000000) 235 188
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t152 : ((184967273601/2500000000000 : ℚ) : ℝ) ≤ stT235 152 := by
  have hc : ((228043/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184967273601/2500000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((228043/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c153 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((436701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2797169/10000000) (δ := 11851/1000000000) (ψ := -204787/1000000) 235 188
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t153 : ((88252843563/2500000000000 : ℚ) : ℝ) ≤ stT235 153 := by
  have hc : ((436651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88252843563/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((436651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c154 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-440749/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1324911/2000000) (δ := 1469/125000000) (ψ := -204787/1000000) 235 188
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t154 : ((-177592913501/2500000000000 : ℚ) : ℝ) ≤ stT235 154 := by
  have hc : ((-220387/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177592913501/2500000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-220387/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c155 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-515447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1056163/2000000) (δ := 2389/200000000) (ψ := -204787/1000000) 235 189
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t155 : ((-20702875017/500000000000 : ℚ) : ℝ) ≤ stT235 155 := by
  have hc : ((-515497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20702875017/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-515497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c156 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((412367/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1502661/10000000) (δ := 2369/200000000) (ψ := -204787/1000000) 235 189
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t156 : ((257919921/3906250000 : ℚ) : ℝ) ≤ stT235 156 := by
  have hc : ((206171/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((257919921/3906250000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((206171/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c157 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((155297/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2251347/10000000) (δ := 5929/500000000) (ψ := -204787/1000000) 235 189
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t157 : ((123930385467/2500000000000 : ℚ) : ℝ) ≤ stT235 157 := by
  have hc : ((310569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123930385467/2500000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((310569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c158 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-91547/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2990751/5000000) (δ := 5929/500000000) (ψ := -204787/1000000) 235 189
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t158 : ((-145671840927/2500000000000 : ℚ) : ℝ) ≤ stT235 158 := by
  have hc : ((-366213/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145671840927/2500000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-366213/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c159 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-371361/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6019807/10000000) (δ := 11937/1000000000) (ψ := -204787/1000000) 235 190
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t159 : ((-36816051259/625000000000 : ℚ) : ℝ) ≤ stT235 159 := by
  have hc : ((-185693/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36816051259/625000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-185693/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c160 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((594167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2336417/10000000) (δ := 11937/1000000000) (ψ := -204787/1000000) 235 190
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t160 : ((469690482573/10000000000000 : ℚ) : ℝ) ≤ stT235 160 := by
  have hc : ((594117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((469690482573/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((594117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c161 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((863009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 662001/5000000) (δ := 11837/1000000000) (ψ := -204787/1000000) 235 190
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t161 : ((68010661749/1000000000000 : ℚ) : ℝ) ≤ stT235 161 := by
  have hc : ((862959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68010661749/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((862959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c162 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-80441/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2480901/5000000) (δ := 11837/1000000000) (ψ := -204787/1000000) 235 190
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t162 : ((-2528333577/80000000000 : ℚ) : ℝ) ≤ stT235 162 := by
  have hc : ((-80451/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2528333577/80000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-80451/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c163 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-191689/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1426149/2000000) (δ := 1183/100000000) (ψ := -204787/1000000) 235 191
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t163 : ((-150150350439/2000000000000 : ℚ) : ℝ) ≤ stT235 163 := by
  have hc : ((-191699/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-150150350439/2000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-191699/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c164 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((19397/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3537477/10000000) (δ := 11873/1000000000) (ψ := -204787/1000000) 235 191
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t164 : ((15141616171/1250000000000 : ℚ) : ℝ) ≤ stT235 164 := by
  have hc : ((77563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15141616171/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((77563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c165 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((249977/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6787/2000000) (δ := 1183/100000000) (ψ := -204787/1000000) 235 191
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t165 : ((194596863321/2500000000000 : ℚ) : ℝ) ≤ stT235 165 := by
  have hc : ((499929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194596863321/2500000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((499929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c166 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((136851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1791893/5000000) (δ := 1193/100000000) (ψ := -204787/1000000) 235 191
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t166 : ((2123561923/200000000000 : ℚ) : ℝ) ≤ stT235 166 := by
  have hc : ((136801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2123561923/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((136801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c167 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-956323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 711237/1000000) (δ := 1183/100000000) (ψ := -204787/1000000) 235 191
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t167 : ((-11563505943/156250000000 : ℚ) : ℝ) ≤ stT235 167 := by
  have hc : ((-956373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11563505943/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-956373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c168 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-447947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5088159/10000000) (δ := 297/25000000) (ψ := -204787/1000000) 235 192
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t168 : ((-345637301449/10000000000000 : ℚ) : ℝ) ≤ stT235 168 := by
  have hc : ((-447997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-345637301449/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-447997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c169 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((400873/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -200183/1250000) (δ := 297/25000000) (ψ := -204787/1000000) 235 192
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t169 : ((1927151919/31250000000 : ℚ) : ℝ) ≤ stT235 169 := by
  have hc : ((25053/31250 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1927151919/31250000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((25053/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c170 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((183629/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1864609/10000000) (δ := 11923/1000000000) (ψ := -204787/1000000) 235 192
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t170 : ((70413622653/1250000000000 : ℚ) : ℝ) ≤ stT235 170 := by
  have hc : ((367233/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70413622653/1250000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((367233/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c171 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-525537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1327589/2500000) (δ := 297/25000000) (ψ := -204787/1000000) 235 192
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t171 : ((-5024086133/125000000000 : ℚ) : ℝ) ≤ stT235 171 := by
  have hc : ((-525587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5024086133/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-525587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c172 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-187681/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3485977/5000000) (δ := 1477/125000000) (ψ := -204787/1000000) 235 193
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t172 : ((-143113073663/2000000000000 : ℚ) : ℝ) ≤ stT235 172 := by
  have hc : ((-187691/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143113073663/2000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-187691/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c173 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((143833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1783079/5000000) (δ := 2979/250000000) (ψ := -204787/1000000) 235 193
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t173 : ((21863211631/2000000000000 : ℚ) : ℝ) ≤ stT235 173 := by
  have hc : ((143783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21863211631/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((143783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c174 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((99741/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11249/625000) (δ := 1477/125000000) (ψ := -204787/1000000) 235 193
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t174 : ((4725603883/62500000000 : ℚ) : ℝ) ≤ stT235 174 := by
  have hc : ((12467/12500 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4725603883/62500000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((12467/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c175 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((291769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1593401/5000000) (δ := 2979/250000000) (ψ := -204787/1000000) 235 193
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t175 : ((27564820029/1250000000000 : ℚ) : ℝ) ≤ stT235 175 := by
  have hc : ((291719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27564820029/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((291719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c176 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-107987/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6534377/10000000) (δ := 2979/250000000) (ψ := -204787/1000000) 235 193
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t176 : ((-325612175967/5000000000000 : ℚ) : ℝ) ≤ stT235 176 := by
  have hc : ((-431973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-325612175967/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-431973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c177 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-86763/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -91327/156250) (δ := 5947/500000000) (ψ := -204787/1000000) 235 194
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t177 : ((-260879385819/5000000000000 : ℚ) : ℝ) ≤ stT235 177 := by
  have hc : ((-347077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-260879385819/5000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-347077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c178 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((105689/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2535071/10000000) (δ := 11809/1000000000) (ψ := -204787/1000000) 235 194
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t178 : ((79209686549/2000000000000 : ℚ) : ℝ) ≤ stT235 178 := by
  have hc : ((105679/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79209686549/2000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((105679/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c179 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((954591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18907/250000) (δ := 11909/1000000000) (ψ := -204787/1000000) 235 194
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t179 : ((142691470467/2000000000000 : ℚ) : ℝ) ≤ stT235 179 := by
  have hc : ((954541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142691470467/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((954541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c180 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-40889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4029243/10000000) (δ := 5897/500000000) (ψ := -204787/1000000) 235 194
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t180 : ((-7628532321/2500000000000 : ℚ) : ℝ) ≤ stT235 180 := by
  have hc : ((-40939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7628532321/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-40939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c181 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-243533/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 728411/1000000) (δ := 11909/1000000000) (ψ := -204787/1000000) 235 194
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t181 : ((-72410460969/1000000000000 : ℚ) : ℝ) ≤ stT235 181 := by
  have hc : ((-487091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72410460969/1000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-487091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c182 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-241461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5186963/10000000) (δ := 11801/1000000000) (ψ := -204787/1000000) 235 195
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t182 : ((-71600599/2000000000 : ℚ) : ℝ) ≤ stT235 182 := by
  have hc : ((-120743/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71600599/2000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-120743/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c183 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((7059/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1967757/10000000) (δ := 11901/1000000000) (ψ := -204787/1000000) 235 195
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t183 : ((10435582857/200000000000 : ℚ) : ℝ) ≤ stT235 183 := by
  have hc : ((14117/20000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10435582857/200000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((14117/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c184 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((176131/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1233883/10000000) (δ := 11901/1000000000) (ψ := -204787/1000000) 235 195
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t184 : ((129837986289/2000000000000 : ℚ) : ℝ) ≤ stT235 184 := by
  have hc : ((176121/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129837986289/2000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((176121/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c185 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-195219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 276137/625000) (δ := 11801/1000000000) (ψ := -204787/1000000) 235 195
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t185 : ((-28712939567/2000000000000 : ℚ) : ℝ) ≤ stT235 185 := by
  have hc : ((-195269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28712939567/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-195269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c186 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-99423/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7585287/10000000) (δ := 11801/1000000000) (ψ := -204787/1000000) 235 195
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t186 : ((-4556511813/62500000000 : ℚ) : ℝ) ≤ stT235 186 := by
  have hc : ((-24857/25000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4556511813/62500000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-24857/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c187 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-10153/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4972501/10000000) (δ := 11809/1000000000) (ψ := -204787/1000000) 235 196
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t187 : ((-29702115441/1000000000000 : ℚ) : ℝ) ≤ stT235 187 := by
  have hc : ((-40617/100000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29702115441/1000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-40617/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c188 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((370689/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1839187/10000000) (δ := 11909/1000000000) (ψ := -204787/1000000) 235 196
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t188 : ((8447942223/156250000000 : ℚ) : ℝ) ≤ stT235 188 := by
  have hc : ((46333/62500 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8447942223/156250000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((46333/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c189 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((218061/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1277559/10000000) (δ := 11809/1000000000) (ψ := -204787/1000000) 235 196
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t189 : ((9912920907/156250000000 : ℚ) : ℝ) ≤ stT235 189 := by
  have hc : ((436097/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9912920907/156250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((436097/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c190 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-89673/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1094449/2500000) (δ := 5947/500000000) (ψ := -204787/1000000) 235 196
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t190 : ((-32536917973/2500000000000 : ℚ) : ℝ) ≤ stT235 190 := by
  have hc : ((-44849/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32536917973/2500000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-44849/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c191 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-493861/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7461819/10000000) (δ := 11809/1000000000) (ψ := -204787/1000000) 235 196
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t191 : ((-7147271249/100000000000 : ℚ) : ℝ) ≤ stT235 191 := by
  have hc : ((-246943/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7147271249/100000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-246943/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c192 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-479877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2589139/5000000) (δ := 1477/125000000) (ψ := -204787/1000000) 235 197
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t192 : ((-43294694597/1250000000000 : ℚ) : ℝ) ≤ stT235 192 := by
  have hc : ((-479927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43294694597/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-479927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c193 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((329791/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2126333/10000000) (δ := 1477/125000000) (ψ := -204787/1000000) 235 197
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t193 : ((23737051329/500000000000 : ℚ) : ℝ) ≤ stT235 193 := by
  have hc : ((164883/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23737051329/500000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((164883/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c194 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((934499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 909867/10000000) (δ := 1477/125000000) (ψ := -204787/1000000) 235 197
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t194 : ((335447567571/5000000000000 : ℚ) : ℝ) ≤ stT235 194 := by
  have hc : ((934449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((335447567571/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((934449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c195 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-1379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3930439/10000000) (δ := 11887/1000000000) (ψ := -204787/1000000) 235 197
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t195 : ((-204665667/2000000000000 : ℚ) : ℝ) ≤ stT235 195 := by
  have hc : ((-1429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204665667/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-1429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c196 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-233319/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6935561/10000000) (δ := 2979/250000000) (ψ := -204787/1000000) 235 197
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t196 : ((-166665423809/2500000000000 : ℚ) : ℝ) ≤ stT235 196 := by
  have hc : ((-466663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166665423809/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-466663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c197 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-67593/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1445639/2500000) (δ := 11923/1000000000) (ψ := -204787/1000000) 235 198
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t197 : ((-24080807329/500000000000 : ℚ) : ℝ) ≤ stT235 197 := by
  have hc : ((-33799/50000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24080807329/500000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-33799/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c198 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((432847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -701967/2500000) (δ := 297/25000000) (ψ := -204787/1000000) 235 198
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t198 : ((307575411193/10000000000000 : ℚ) : ℝ) ≤ stT235 198 := by
  have hc : ((432797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((307575411193/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((432797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c199 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((249539/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 949/62500) (δ := 11823/1000000000) (ψ := -204787/1000000) 235 198
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t199 : ((353769189693/5000000000000 : ℚ) : ℝ) ≤ stT235 199 := by
  have hc : ((499053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((353769189693/5000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((499053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c200 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((6521/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 774171/2500000) (δ := 11923/1000000000) (ψ := -204787/1000000) 235 198
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t200 : ((57629139/2500000000 : ℚ) : ℝ) ≤ stT235 200 := by
  have hc : ((163/500 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57629139/2500000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((163/500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c201 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-744619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6026899/10000000) (δ := 11923/1000000000) (ψ := -204787/1000000) 235 198
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t201 : ((-262624650237/5000000000000 : ℚ) : ℝ) ≤ stT235 201 := by
  have hc : ((-744669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-262624650237/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-744669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c202 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-906701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3382739/5000000) (δ := 1193/100000000) (ψ := -204787/1000000) 235 199
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t202 : ((-318994095049/5000000000000 : ℚ) : ℝ) ≤ stT235 202 := by
  have hc : ((-906751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-318994095049/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-906751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c203 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((25103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3864227/10000000) (δ := 1183/100000000) (ψ := -204787/1000000) 235 199
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t203 : ((8791874343/5000000000000 : ℚ) : ℝ) ≤ stT235 203 := by
  have hc : ((25053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8791874343/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((25053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c204 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((462283/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -244313/2500000) (δ := 1183/100000000) (ψ := -204787/1000000) 235 199
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t204 : ((8091132903/125000000000 : ℚ) : ℝ) ≤ stT235 204 := by
  have hc : ((231129/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8091132903/125000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((231129/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c205 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((726041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1895623/10000000) (δ := 1183/100000000) (ψ := -204787/1000000) 235 199
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t205 : ((50705389413/1000000000000 : ℚ) : ℝ) ≤ stT235 205 := by
  have hc : ((725991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50705389413/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((725991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c206 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-162499/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 950903/2000000) (δ := 11873/1000000000) (ψ := -204787/1000000) 235 199
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t206 : ((-14154499577/625000000000 : ℚ) : ℝ) ≤ stT235 206 := by
  have hc : ((-40631/125000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14154499577/625000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-40631/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c207 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-39793/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7599543/10000000) (δ := 1183/100000000) (ψ := -204787/1000000) 235 199
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t207 : ((-5531894991/80000000000 : ℚ) : ℝ) ≤ stT235 207 := by
  have hc : ((-7959/8000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5531894991/80000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-7959/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c208 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-514167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2638541/5000000) (δ := 5933/500000000) (ψ := -204787/1000000) 235 200
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t208 : ((-2785513489/78125000000 : ℚ) : ℝ) ≤ stT235 208 := by
  have hc : ((-514217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2785513489/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-514217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c209 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((22157/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1229657/5000000) (δ := 11837/1000000000) (ψ := -204787/1000000) 235 200
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t209 : ((1532492367/40000000000 : ℚ) : ℝ) ≤ stT235 209 := by
  have hc : ((4431/8000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1532492367/40000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((4431/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c210 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((990493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69/2000) (δ := 11937/1000000000) (ψ := -204787/1000000) 235 200
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t210 : ((136694009759/2000000000000 : ℚ) : ℝ) ≤ stT235 210 := by
  have hc : ((990443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136694009759/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((990443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c211 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((311153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3135977/10000000) (δ := 5883/500000000) (ψ := -204787/1000000) 235 200
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t211 : ((53543004021/2500000000000 : ℚ) : ℝ) ≤ stT235 211 := by
  have hc : ((311103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53543004021/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((311103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c212 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-178413/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 739217/1250000) (δ := 11837/1000000000) (ψ := -204787/1000000) 235 200
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t212 : ((-245086337353/5000000000000 : ℚ) : ℝ) ≤ stT235 212 := by
  have hc : ((-356851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245086337353/5000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-356851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c213 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-946111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7029511/10000000) (δ := 2369/200000000) (ψ := -204787/1000000) 235 201
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t213 : ((-648299109429/10000000000000 : ℚ) : ℝ) ≤ stT235 213 := by
  have hc : ((-946161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-648299109429/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-946161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c214 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-17479/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -106943/250000) (δ := 5879/500000000) (ψ := -204787/1000000) 235 201
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t214 : ((-23905344213/2500000000000 : ℚ) : ℝ) ≤ stT235 214 := by
  have hc : ((-69941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23905344213/2500000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-69941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c215 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((408237/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -307759/2000000) (δ := 5879/500000000) (ψ := -204787/1000000) 235 201
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t215 : ((34799766841/625000000000 : ℚ) : ℝ) ≤ stT235 215 := by
  have hc : ((102053/125000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34799766841/625000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((102053/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c216 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((111163/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14843/125000) (δ := 5879/500000000) (ψ := -204787/1000000) 235 201
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t216 : ((302529990951/5000000000000 : ℚ) : ℝ) ≤ stT235 216 := by
  have hc : ((444627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((302529990951/5000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((444627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c217 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((10379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 975261/2500000) (δ := 2369/200000000) (ψ := -204787/1000000) 235 201
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t217 : ((1752944919/2500000000000 : ℚ) : ℝ) ≤ stT235 217 := by
  have hc : ((10329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1752944919/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((10329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c218 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-877239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6602193/10000000) (δ := 2389/200000000) (ψ := -204787/1000000) 235 201
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t218 : ((-297087778827/5000000000000 : ℚ) : ℝ) ≤ stT235 218 := by
  have hc : ((-877289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-297087778827/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-877289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c219 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-13114/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20053/31250) (δ := 11951/1000000000) (ψ := -204787/1000000) 235 202
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t219 : ((-141794496837/2500000000000 : ℚ) : ℝ) ≤ stT235 219 := by
  have hc : ((-419673/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141794496837/2500000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-419673/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c220 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((18639/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3740427/10000000) (δ := 1469/125000000) (ψ := -204787/1000000) 235 202
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t220 : ((25115935347/5000000000000 : ℚ) : ℝ) ≤ stT235 220 := by
  have hc : ((37253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25115935347/5000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((37253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c221 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((908799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1075997/10000000) (δ := 1469/125000000) (ψ := -204787/1000000) 235 202
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t221 : ((19102812729/312500000000 : ℚ) : ℝ) ≤ stT235 221 := by
  have hc : ((908749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19102812729/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((908749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c222 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((403857/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 157633/1000000) (δ := 11951/1000000000) (ψ := -204787/1000000) 235 202
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t222 : ((8469820931/156250000000 : ℚ) : ℝ) ≤ stT235 222 := by
  have hc : ((50479/62500 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8469820931/156250000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((50479/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c223 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-5783/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 421679/1000000) (δ := 11951/1000000000) (ψ := -204787/1000000) 235 202
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t223 : ((-154970403/20000000000 : ℚ) : ℝ) ≤ stT235 223 := by
  have hc : ((-11571/100000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154970403/20000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-11571/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c224 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-36789/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3422721/5000000) (δ := 2963/250000000) (ψ := -204787/1000000) 235 202
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t224 : ((-12291026907/200000000000 : ℚ) : ℝ) ≤ stT235 224 := by
  have hc : ((-36791/40000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12291026907/200000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-36791/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c225 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-10001/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3122781/5000000) (δ := 1493/125000000) (ψ := -204787/1000000) 235 203
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t225 : ((-53342026671/1000000000000 : ℚ) : ℝ) ≤ stT235 225 := by
  have hc : ((-80013/100000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53342026671/1000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-80013/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c226 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((2861/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3640263/10000000) (δ := 23659/1000000000) (ψ := -204787/1000000) 235 203
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t226 : ((760910841/100000000000 : ℚ) : ℝ) ≤ stT235 226 := by
  have hc : ((11439/100000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((760910841/100000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((11439/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c227 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((114209/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -523211/5000000) (δ := 1493/125000000) (ψ := -204787/1000000) 235 203
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t227 : ((303195967353/5000000000000 : ℚ) : ℝ) ≤ stT235 227 := by
  have hc : ((456811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((303195967353/5000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((456811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c228 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((817121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1535993/10000000) (δ := 1493/125000000) (ψ := -204787/1000000) 235 203
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t228 : ((270559171443/5000000000000 : ℚ) : ℝ) ≤ stT235 228 := by
  have hc : ((817071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270559171443/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((817071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c229 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-71993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 513391/1250000) (δ := 1493/125000000) (ψ := -204787/1000000) 235 203
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t229 : ((-47607383217/10000000000000 : ℚ) : ℝ) ≤ stT235 229 := by
  have hc : ((-72043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47607383217/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-72043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c230 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-177879/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3333521/5000000) (δ := 2961/250000000) (ψ := -204787/1000000) 235 203
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t230 : ((-117296626709/2000000000000 : ℚ) : ℝ) ≤ stT235 230 := by
  have hc : ((-177889/200000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117296626709/2000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-177889/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c231 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-427629/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6492111/10000000) (δ := 5883/500000000) (ψ := -204787/1000000) 235 204
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t231 : ((-4396496947/78125000000 : ℚ) : ℝ) ≤ stT235 231 := by
  have hc : ((-213827/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4396496947/78125000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-213827/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c232 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-5471/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1977173/5000000) (δ := 5883/500000000) (ψ := -204787/1000000) 235 204
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t232 : ((-451038171/625000000000 : ℚ) : ℝ) ≤ stT235 232 := by
  have hc : ((-687/62500 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-451038171/625000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-687/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c233 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((210343/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28549/200000) (δ := 11837/1000000000) (ψ := -204787/1000000) 235 204
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t233 : ((275583854981/5000000000000 : ℚ) : ℝ) ≤ stT235 233 := by
  have hc : ((420661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((275583854981/5000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((420661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c234 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((453339/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 272159/2500000) (δ := 11937/1000000000) (ψ := -204787/1000000) 235 204
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t234 : ((3704255351/62500000000 : ℚ) : ℝ) ≤ stT235 234 := by
  have hc : ((226657/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3704255351/62500000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((226657/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c235 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((66407/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3593971/10000000) (δ := 11937/1000000000) (ψ := -204787/1000000) 235 204
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t235 : ((2706427331/312500000000 : ℚ) : ℝ) ≤ stT235 235 := by
  have hc : ((33191/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2706427331/312500000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((33191/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c236 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-760883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6088673/10000000) (δ := 5933/500000000) (ψ := -204787/1000000) 235 204
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t236 : ((-99065106337/2000000000000 : ℚ) : ℝ) ≤ stT235 236 := by
  have hc : ((-760933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99065106337/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-760933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c237 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-239737/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1783791/2500000) (δ := 11873/1000000000) (ψ := -204787/1000000) 235 205
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t237 : ((-31146816543/500000000000 : ℚ) : ℝ) ≤ stT235 237 := by
  have hc : ((-479499/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31146816543/500000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-479499/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c238 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-289593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -582687/1250000) (δ := 1193/100000000) (ψ := -204787/1000000) 235 205
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t238 : ((-46936937793/2500000000000 : ℚ) : ℝ) ≤ stT235 238 := by
  have hc : ((-289643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46936937793/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-289643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c239 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((159429/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2198167/10000000) (δ := 1183/100000000) (ψ := -204787/1000000) 235 205
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t239 : ((103117925359/2500000000000 : ℚ) : ℝ) ≤ stT235 239 := by
  have hc : ((318833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103117925359/2500000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((318833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c240 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((994807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 254881/10000000) (δ := 11873/1000000000) (ψ := -204787/1000000) 235 205
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t240 : ((642112659229/10000000000000 : ℚ) : ℝ) ≤ stT235 240 := by
  have hc : ((994757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((642112659229/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((994757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c241 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((472137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1348853/5000000) (δ := 11873/1000000000) (ψ := -204787/1000000) 235 205
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t241 : ((76024418393/2500000000000 : ℚ) : ℝ) ≤ stT235 241 := by
  have hc : ((472087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76024418393/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((472087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c242 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-231499/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2565213/5000000) (δ := 11873/1000000000) (ψ := -204787/1000000) 235 205
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t242 : ((-1488294153/50000000000 : ℚ) : ℝ) ≤ stT235 242 := by
  have hc : ((-57881/125000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1488294153/50000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-57881/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c243 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-496383/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7553099/10000000) (δ := 1193/100000000) (ψ := -204787/1000000) 235 205
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t243 : ((-39805778551/625000000000 : ℚ) : ℝ) ≤ stT235 243 := by
  have hc : ((-62051/62500 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39805778551/625000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-62051/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c244 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-331961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5742119/10000000) (δ := 11823/1000000000) (ψ := -204787/1000000) 235 206
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t244 : ((-21253245741/500000000000 : ℚ) : ℝ) ≤ stT235 244 := by
  have hc : ((-165993/250000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21253245741/500000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-165993/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c245 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((7279/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3339273/10000000) (δ := 1179/50000000) (ψ := -204787/1000000) 235 206
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t245 : ((18597520641/1250000000000 : ℚ) : ℝ) ≤ stT235 245 := by
  have hc : ((116439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18597520641/1250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((116439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c246 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((92923/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47309/500000) (δ := 589/50000000) (ψ := -204787/1000000) 235 206
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t246 : ((3702642923/62500000000 : ℚ) : ℝ) ≤ stT235 246 := by
  have hc : ((46459/50000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3702642923/62500000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((46459/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c247 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((41963/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143719/1000000) (δ := 589/50000000) (ψ := -204787/1000000) 235 206
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t247 : ((13349397391/250000000000 : ℚ) : ℝ) ≤ stT235 247 := by
  have hc : ((83921/100000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13349397391/250000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((83921/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c248 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((4641/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 152437/400000) (δ := 589/50000000) (ψ := -204787/1000000) 235 206
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t248 : ((147193/50000000 : ℚ) : ℝ) ≤ stT235 248 := by
  have hc : ((1159/25000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147193/50000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((1159/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c249 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-782853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1543771/2500000) (δ := 297/25000000) (ψ := -204787/1000000) 235 206
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t249 : ((-19845808147/400000000000 : ℚ) : ℝ) ≤ stT235 249 := by
  have hc : ((-782903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19845808147/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-782903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_c250 :
    |Real.cos (((235 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-963679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7178121/10000000) (δ := 2363/200000000) (ψ := -204787/1000000) 235 207
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st235_t250 : ((-76189523553/1250000000000 : ℚ) : ℝ) ≤ stT235 250 := by
  have hc : ((-963729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((235 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st235_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76189523553/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-963729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st235_p1 : ((489527/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT235 (i+1) := by
  rw [Finset.sum_range_one]
  exact st235_t1

theorem st235_p2 : ((16607989039911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT235 (i+1))
      = (∑ i ∈ Finset.range 1, stT235 (i+1)) + stT235 2 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 1
    simpa using h
  have hprev := st235_p1
  have hstep := st235_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p3 : ((20760314772319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT235 (i+1))
      = (∑ i ∈ Finset.range 2, stT235 (i+1)) + stT235 3 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 2
    simpa using h
  have hprev := st235_p2
  have hstep := st235_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p4 : ((24446749772319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT235 (i+1))
      = (∑ i ∈ Finset.range 3, stT235 (i+1)) + stT235 4 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 3
    simpa using h
  have hprev := st235_p3
  have hstep := st235_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p5 : ((25067079618169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT235 (i+1))
      = (∑ i ∈ Finset.range 4, stT235 (i+1)) + stT235 5 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 4
    simpa using h
  have hprev := st235_p4
  have hstep := st235_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p6 : ((5794638046161/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT235 (i+1))
      = (∑ i ∈ Finset.range 5, stT235 (i+1)) + stT235 6 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 5
    simpa using h
  have hprev := st235_p5
  have hstep := st235_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p7 : ((30416761002657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT235 (i+1))
      = (∑ i ∈ Finset.range 6, stT235 (i+1)) + stT235 7 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 6
    simpa using h
  have hprev := st235_p6
  have hstep := st235_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p8 : ((31648462918131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT235 (i+1))
      = (∑ i ∈ Finset.range 7, stT235 (i+1)) + stT235 8 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 7
    simpa using h
  have hprev := st235_p7
  have hstep := st235_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p9 : ((32438809505763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT235 (i+1))
      = (∑ i ∈ Finset.range 8, stT235 (i+1)) + stT235 9 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 8
    simpa using h
  have hprev := st235_p8
  have hstep := st235_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p10 : ((685131687119/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT235 (i+1))
      = (∑ i ∈ Finset.range 9, stT235 (i+1)) + stT235 10 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 9
    simpa using h
  have hprev := st235_p9
  have hstep := st235_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p11 : ((8410139342317/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT235 (i+1))
      = (∑ i ∈ Finset.range 10, stT235 (i+1)) + stT235 11 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 10
    simpa using h
  have hprev := st235_p10
  have hstep := st235_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p12 : ((729627141337/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT235 (i+1))
      = (∑ i ∈ Finset.range 11, stT235 (i+1)) + stT235 12 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 11
    simpa using h
  have hprev := st235_p11
  have hstep := st235_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p13 : ((783782613277/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT235 (i+1))
      = (∑ i ∈ Finset.range 12, stT235 (i+1)) + stT235 13 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 12
    simpa using h
  have hprev := st235_p12
  have hstep := st235_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p14 : ((7794398844133/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT235 (i+1))
      = (∑ i ∈ Finset.range 13, stT235 (i+1)) + stT235 14 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 13
    simpa using h
  have hprev := st235_p13
  have hstep := st235_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p15 : ((758188307551/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT235 (i+1))
      = (∑ i ∈ Finset.range 14, stT235 (i+1)) + stT235 15 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 14
    simpa using h
  have hprev := st235_p14
  have hstep := st235_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p16 : ((37616632760437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT235 (i+1))
      = (∑ i ∈ Finset.range 15, stT235 (i+1)) + stT235 16 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 15
    simpa using h
  have hprev := st235_p15
  have hstep := st235_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p17 : ((40041794731957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT235 (i+1))
      = (∑ i ∈ Finset.range 16, stT235 (i+1)) + stT235 17 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 16
    simpa using h
  have hprev := st235_p16
  have hstep := st235_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p18 : ((41582815715557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT235 (i+1))
      = (∑ i ∈ Finset.range 17, stT235 (i+1)) + stT235 18 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 17
    simpa using h
  have hprev := st235_p17
  have hstep := st235_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p19 : ((10706738278939/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT235 (i+1))
      = (∑ i ∈ Finset.range 18, stT235 (i+1)) + stT235 19 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 18
    simpa using h
  have hprev := st235_p18
  have hstep := st235_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p20 : ((44804917610147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT235 (i+1))
      = (∑ i ∈ Finset.range 19, stT235 (i+1)) + stT235 20 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 19
    simpa using h
  have hprev := st235_p19
  have hstep := st235_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p21 : ((46586445547169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT235 (i+1))
      = (∑ i ∈ Finset.range 20, stT235 (i+1)) + stT235 21 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 20
    simpa using h
  have hprev := st235_p20
  have hstep := st235_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p22 : ((45247510411041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT235 (i+1))
      = (∑ i ∈ Finset.range 21, stT235 (i+1)) + stT235 22 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 21
    simpa using h
  have hprev := st235_p21
  have hstep := st235_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p23 : ((44547206122211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT235 (i+1))
      = (∑ i ∈ Finset.range 22, stT235 (i+1)) + stT235 23 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 22
    simpa using h
  have hprev := st235_p22
  have hstep := st235_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p24 : ((46170111109189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT235 (i+1))
      = (∑ i ∈ Finset.range 23, stT235 (i+1)) + stT235 24 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 23
    simpa using h
  have hprev := st235_p23
  have hstep := st235_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p25 : ((8879800444727/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT235 (i+1))
      = (∑ i ∈ Finset.range 24, stT235 (i+1)) + stT235 25 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 24
    simpa using h
  have hprev := st235_p24
  have hstep := st235_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p26 : ((4591002774511/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT235 (i+1))
      = (∑ i ∈ Finset.range 25, stT235 (i+1)) + stT235 26 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 25
    simpa using h
  have hprev := st235_p25
  have hstep := st235_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p27 : ((22648752632417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT235 (i+1))
      = (∑ i ∈ Finset.range 26, stT235 (i+1)) + stT235 27 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 26
    simpa using h
  have hprev := st235_p26
  have hstep := st235_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p28 : ((2215118302457/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT235 (i+1))
      = (∑ i ∈ Finset.range 27, stT235 (i+1)) + stT235 28 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 27
    simpa using h
  have hprev := st235_p27
  have hstep := st235_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p29 : ((46134901974143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT235 (i+1))
      = (∑ i ∈ Finset.range 28, stT235 (i+1)) + stT235 29 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 28
    simpa using h
  have hprev := st235_p28
  have hstep := st235_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p30 : ((46224538554279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT235 (i+1))
      = (∑ i ∈ Finset.range 29, stT235 (i+1)) + stT235 30 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 29
    simpa using h
  have hprev := st235_p29
  have hstep := st235_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p31 : ((8892663445111/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT235 (i+1))
      = (∑ i ∈ Finset.range 30, stT235 (i+1)) + stT235 31 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 30
    simpa using h
  have hprev := st235_p30
  have hstep := st235_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p32 : ((4347889197743/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT235 (i+1))
      = (∑ i ∈ Finset.range 31, stT235 (i+1)) + stT235 32 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 31
    simpa using h
  have hprev := st235_p31
  have hstep := st235_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p33 : ((22044047843583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT235 (i+1))
      = (∑ i ∈ Finset.range 32, stT235 (i+1)) + stT235 33 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 32
    simpa using h
  have hprev := st235_p32
  have hstep := st235_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p34 : ((22804221804773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT235 (i+1))
      = (∑ i ∈ Finset.range 33, stT235 (i+1)) + stT235 34 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 33
    simpa using h
  have hprev := st235_p33
  have hstep := st235_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p35 : ((23648362465127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT235 (i+1))
      = (∑ i ∈ Finset.range 34, stT235 (i+1)) + stT235 35 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 34
    simpa using h
  have hprev := st235_p34
  have hstep := st235_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p36 : ((12210340661433/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT235 (i+1))
      = (∑ i ∈ Finset.range 35, stT235 (i+1)) + stT235 36 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 35
    simpa using h
  have hprev := st235_p35
  have hstep := st235_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p37 : ((10050186064451/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT235 (i+1))
      = (∑ i ∈ Finset.range 36, stT235 (i+1)) + stT235 37 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 36
    simpa using h
  have hprev := st235_p36
  have hstep := st235_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p38 : ((51655133360581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT235 (i+1))
      = (∑ i ∈ Finset.range 37, stT235 (i+1)) + stT235 38 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 37
    simpa using h
  have hprev := st235_p37
  have hstep := st235_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p39 : ((10632353809159/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT235 (i+1))
      = (∑ i ∈ Finset.range 38, stT235 (i+1)) + stT235 39 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 38
    simpa using h
  have hprev := st235_p38
  have hstep := st235_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p40 : ((54742715728097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT235 (i+1))
      = (∑ i ∈ Finset.range 39, stT235 (i+1)) + stT235 40 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 39
    simpa using h
  have hprev := st235_p39
  have hstep := st235_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p41 : ((2806803234151/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT235 (i+1))
      = (∑ i ∈ Finset.range 40, stT235 (i+1)) + stT235 41 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 40
    simpa using h
  have hprev := st235_p40
  have hstep := st235_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p42 : ((56851274365817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT235 (i+1))
      = (∑ i ∈ Finset.range 41, stT235 (i+1)) + stT235 42 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 41
    simpa using h
  have hprev := st235_p41
  have hstep := st235_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p43 : ((56442218221121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT235 (i+1))
      = (∑ i ∈ Finset.range 42, stT235 (i+1)) + stT235 43 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 42
    simpa using h
  have hprev := st235_p42
  have hstep := st235_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p44 : ((27532385464003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT235 (i+1))
      = (∑ i ∈ Finset.range 43, stT235 (i+1)) + stT235 44 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 43
    simpa using h
  have hprev := st235_p43
  have hstep := st235_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p45 : ((26910295693927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT235 (i+1))
      = (∑ i ∈ Finset.range 44, stT235 (i+1)) + stT235 45 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 44
    simpa using h
  have hprev := st235_p44
  have hstep := st235_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p46 : ((10802561983693/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT235 (i+1))
      = (∑ i ∈ Finset.range 45, stT235 (i+1)) + stT235 46 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 45
    simpa using h
  have hprev := st235_p45
  have hstep := st235_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p47 : ((55439097331751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT235 (i+1))
      = (∑ i ∈ Finset.range 46, stT235 (i+1)) + stT235 47 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 46
    simpa using h
  have hprev := st235_p46
  have hstep := st235_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p48 : ((14015397221219/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT235 (i+1))
      = (∑ i ∈ Finset.range 47, stT235 (i+1)) + stT235 48 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 47
    simpa using h
  have hprev := st235_p47
  have hstep := st235_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p49 : ((6858231586537/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT235 (i+1))
      = (∑ i ∈ Finset.range 48, stT235 (i+1)) + stT235 49 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 48
    simpa using h
  have hprev := st235_p48
  have hstep := st235_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p50 : ((6756323325697/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT235 (i+1))
      = (∑ i ∈ Finset.range 49, stT235 (i+1)) + stT235 50 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 49
    simpa using h
  have hprev := st235_p49
  have hstep := st235_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p51 : ((6905023959877/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT235 (i+1))
      = (∑ i ∈ Finset.range 50, stT235 (i+1)) + stT235 51 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 50
    simpa using h
  have hprev := st235_p50
  have hstep := st235_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p52 : ((27894180736633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT235 (i+1))
      = (∑ i ∈ Finset.range 51, stT235 (i+1)) + stT235 52 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 51
    simpa using h
  have hprev := st235_p51
  have hstep := st235_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p53 : ((170108047607/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT235 (i+1))
      = (∑ i ∈ Finset.range 52, stT235 (i+1)) + stT235 53 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 52
    simpa using h
  have hprev := st235_p52
  have hstep := st235_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p54 : ((13659254325517/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT235 (i+1))
      = (∑ i ∈ Finset.range 53, stT235 (i+1)) + stT235 54 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 53
    simpa using h
  have hprev := st235_p53
  have hstep := st235_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p55 : ((55786690605847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT235 (i+1))
      = (∑ i ∈ Finset.range 54, stT235 (i+1)) + stT235 55 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 54
    simpa using h
  have hprev := st235_p54
  have hstep := st235_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p56 : ((54642552570289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT235 (i+1))
      = (∑ i ∈ Finset.range 55, stT235 (i+1)) + stT235 56 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 55
    simpa using h
  have hprev := st235_p55
  have hstep := st235_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p57 : ((54655661463493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT235 (i+1))
      = (∑ i ∈ Finset.range 56, stT235 (i+1)) + stT235 57 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 56
    simpa using h
  have hprev := st235_p56
  have hstep := st235_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p58 : ((55712502032917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT235 (i+1))
      = (∑ i ∈ Finset.range 57, stT235 (i+1)) + stT235 58 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 57
    simpa using h
  have hprev := st235_p57
  have hstep := st235_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p59 : ((54447963257017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT235 (i+1))
      = (∑ i ∈ Finset.range 58, stT235 (i+1)) + stT235 59 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 58
    simpa using h
  have hprev := st235_p58
  have hstep := st235_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p60 : ((55092045327593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT235 (i+1))
      = (∑ i ∈ Finset.range 59, stT235 (i+1)) + stT235 60 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 59
    simpa using h
  have hprev := st235_p59
  have hstep := st235_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p61 : ((55371896641721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT235 (i+1))
      = (∑ i ∈ Finset.range 60, stT235 (i+1)) + stT235 61 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 60
    simpa using h
  have hprev := st235_p60
  have hstep := st235_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p62 : ((10875397192987/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT235 (i+1))
      = (∑ i ∈ Finset.range 61, stT235 (i+1)) + stT235 62 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 61
    simpa using h
  have hprev := st235_p61
  have hstep := st235_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p63 : ((55635082973439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT235 (i+1))
      = (∑ i ∈ Finset.range 62, stT235 (i+1)) + stT235 63 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 62
    simpa using h
  have hprev := st235_p62
  have hstep := st235_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p64 : ((27271127924589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT235 (i+1))
      = (∑ i ∈ Finset.range 63, stT235 (i+1)) + stT235 64 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 63
    simpa using h
  have hprev := st235_p63
  have hstep := st235_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p65 : ((5520305815551/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT235 (i+1))
      = (∑ i ∈ Finset.range 64, stT235 (i+1)) + stT235 65 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 64
    simpa using h
  have hprev := st235_p64
  have hstep := st235_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p66 : ((5506096625157/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT235 (i+1))
      = (∑ i ∈ Finset.range 65, stT235 (i+1)) + stT235 66 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 65
    simpa using h
  have hprev := st235_p65
  have hstep := st235_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p67 : ((5472719429079/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT235 (i+1))
      = (∑ i ∈ Finset.range 66, stT235 (i+1)) + stT235 67 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 66
    simpa using h
  have hprev := st235_p66
  have hstep := st235_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p68 : ((27714204183399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT235 (i+1))
      = (∑ i ∈ Finset.range 67, stT235 (i+1)) + stT235 68 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 67
    simpa using h
  have hprev := st235_p67
  have hstep := st235_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p69 : ((54481044769197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT235 (i+1))
      = (∑ i ∈ Finset.range 68, stT235 (i+1)) + stT235 69 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 68
    simpa using h
  have hprev := st235_p68
  have hstep := st235_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p70 : ((55569739707101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT235 (i+1))
      = (∑ i ∈ Finset.range 69, stT235 (i+1)) + stT235 70 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 69
    simpa using h
  have hprev := st235_p69
  have hstep := st235_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p71 : ((54415106444699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT235 (i+1))
      = (∑ i ∈ Finset.range 70, stT235 (i+1)) + stT235 71 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 70
    simpa using h
  have hprev := st235_p70
  have hstep := st235_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p72 : ((27794482930891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT235 (i+1))
      = (∑ i ∈ Finset.range 71, stT235 (i+1)) + stT235 72 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 71
    simpa using h
  have hprev := st235_p71
  have hstep := st235_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p73 : ((27209286294187/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT235 (i+1))
      = (∑ i ∈ Finset.range 72, stT235 (i+1)) + stT235 73 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 72
    simpa using h
  have hprev := st235_p72
  have hstep := st235_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p74 : ((27789181634407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT235 (i+1))
      = (∑ i ∈ Finset.range 73, stT235 (i+1)) + stT235 74 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 73
    simpa using h
  have hprev := st235_p73
  have hstep := st235_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p75 : ((6803413024471/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT235 (i+1))
      = (∑ i ∈ Finset.range 74, stT235 (i+1)) + stT235 75 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 74
    simpa using h
  have hprev := st235_p74
  have hstep := st235_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p76 : ((27786413379/5000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT235 (i+1))
      = (∑ i ∈ Finset.range 75, stT235 (i+1)) + stT235 76 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 75
    simpa using h
  have hprev := st235_p75
  have hstep := st235_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p77 : ((13608339947483/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT235 (i+1))
      = (∑ i ∈ Finset.range 76, stT235 (i+1)) + stT235 77 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 76
    simpa using h
  have hprev := st235_p76
  have hstep := st235_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p78 : ((27778170397881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT235 (i+1))
      = (∑ i ∈ Finset.range 77, stT235 (i+1)) + stT235 78 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 77
    simpa using h
  have hprev := st235_p77
  have hstep := st235_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p79 : ((27236852870633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT235 (i+1))
      = (∑ i ∈ Finset.range 78, stT235 (i+1)) + stT235 79 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 78
    simpa using h
  have hprev := st235_p78
  have hstep := st235_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p80 : ((1733587474927/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT235 (i+1))
      = (∑ i ∈ Finset.range 79, stT235 (i+1)) + stT235 80 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 79
    simpa using h
  have hprev := st235_p79
  have hstep := st235_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p81 : ((6826665785783/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT235 (i+1))
      = (∑ i ∈ Finset.range 80, stT235 (i+1)) + stT235 81 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 80
    simpa using h
  have hprev := st235_p80
  have hstep := st235_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p82 : ((863484500821/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT235 (i+1))
      = (∑ i ∈ Finset.range 81, stT235 (i+1)) + stT235 82 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 81
    simpa using h
  have hprev := st235_p81
  have hstep := st235_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p83 : ((2196043157329/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT235 (i+1))
      = (∑ i ∈ Finset.range 82, stT235 (i+1)) + stT235 83 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 82
    simpa using h
  have hprev := st235_p82
  have hstep := st235_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p84 : ((10982118645861/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT235 (i+1))
      = (∑ i ∈ Finset.range 83, stT235 (i+1)) + stT235 84 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 83
    simpa using h
  have hprev := st235_p83
  have hstep := st235_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p85 : ((55284222219093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT235 (i+1))
      = (∑ i ∈ Finset.range 84, stT235 (i+1)) + stT235 85 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 84
    simpa using h
  have hprev := st235_p84
  have hstep := st235_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p86 : ((54553282975933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT235 (i+1))
      = (∑ i ∈ Finset.range 85, stT235 (i+1)) + stT235 86 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 85
    simpa using h
  have hprev := st235_p85
  have hstep := st235_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p87 : ((11108036917257/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT235 (i+1))
      = (∑ i ∈ Finset.range 86, stT235 (i+1)) + stT235 87 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 86
    simpa using h
  have hprev := st235_p86
  have hstep := st235_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p88 : ((10895143126409/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT235 (i+1))
      = (∑ i ∈ Finset.range 87, stT235 (i+1)) + stT235 88 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 87
    simpa using h
  have hprev := st235_p87
  have hstep := st235_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p89 : ((55384393820307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT235 (i+1))
      = (∑ i ∈ Finset.range 88, stT235 (i+1)) + stT235 89 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 88
    simpa using h
  have hprev := st235_p88
  have hstep := st235_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p90 : ((27432982265291/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT235 (i+1))
      = (∑ i ∈ Finset.range 89, stT235 (i+1)) + stT235 90 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 89
    simpa using h
  have hprev := st235_p89
  have hstep := st235_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p91 : ((27416840772861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT235 (i+1))
      = (∑ i ∈ Finset.range 90, stT235 (i+1)) + stT235 91 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 90
    simpa using h
  have hprev := st235_p90
  have hstep := st235_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p92 : ((27712880656119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT235 (i+1))
      = (∑ i ∈ Finset.range 91, stT235 (i+1)) + stT235 92 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 91
    simpa using h
  have hprev := st235_p91
  have hstep := st235_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p93 : ((27228672808863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT235 (i+1))
      = (∑ i ∈ Finset.range 92, stT235 (i+1)) + stT235 93 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 92
    simpa using h
  have hprev := st235_p92
  have hstep := st235_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p94 : ((27726698564397/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT235 (i+1))
      = (∑ i ∈ Finset.range 93, stT235 (i+1)) + stT235 94 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 93
    simpa using h
  have hprev := st235_p93
  have hstep := st235_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p95 : ((54829543415991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT235 (i+1))
      = (∑ i ∈ Finset.range 94, stT235 (i+1)) + stT235 95 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 94
    simpa using h
  have hprev := st235_p94
  have hstep := st235_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p96 : ((13700411185239/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT235 (i+1))
      = (∑ i ∈ Finset.range 95, stT235 (i+1)) + stT235 96 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 95
    simpa using h
  have hprev := st235_p95
  have hstep := st235_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p97 : ((27740717059073/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT235 (i+1))
      = (∑ i ∈ Finset.range 96, stT235 (i+1)) + stT235 97 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 96
    simpa using h
  have hprev := st235_p96
  have hstep := st235_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p98 : ((5447688544699/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT235 (i+1))
      = (∑ i ∈ Finset.range 97, stT235 (i+1)) + stT235 98 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 97
    simpa using h
  have hprev := st235_p97
  have hstep := st235_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p99 : ((55276976306987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT235 (i+1))
      = (∑ i ∈ Finset.range 98, stT235 (i+1)) + stT235 99 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 98
    simpa using h
  have hprev := st235_p98
  have hstep := st235_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p100 : ((55136290306987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT235 (i+1))
      = (∑ i ∈ Finset.range 99, stT235 (i+1)) + stT235 100 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 99
    simpa using h
  have hprev := st235_p99
  have hstep := st235_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p101 : ((54524480247269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT235 (i+1))
      = (∑ i ∈ Finset.range 100, stT235 (i+1)) + stT235 101 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 100
    simpa using h
  have hprev := st235_p100
  have hstep := st235_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p102 : ((6938902766467/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT235 (i+1))
      = (∑ i ∈ Finset.range 101, stT235 (i+1)) + stT235 102 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 101
    simpa using h
  have hprev := st235_p101
  have hstep := st235_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p103 : ((27400719340453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT235 (i+1))
      = (∑ i ∈ Finset.range 102, stT235 (i+1)) + stT235 103 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 102
    simpa using h
  have hprev := st235_p102
  have hstep := st235_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p104 : ((10947185016743/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT235 (i+1))
      = (∑ i ∈ Finset.range 103, stT235 (i+1)) + stT235 104 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 103
    simpa using h
  have hprev := st235_p103
  have hstep := st235_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p105 : ((11107016942843/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT235 (i+1))
      = (∑ i ∈ Finset.range 104, stT235 (i+1)) + stT235 105 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 104
    simpa using h
  have hprev := st235_p104
  have hstep := st235_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p106 : ((54607959203491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT235 (i+1))
      = (∑ i ∈ Finset.range 105, stT235 (i+1)) + stT235 106 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 105
    simpa using h
  have hprev := st235_p105
  have hstep := st235_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p107 : ((54923857592739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT235 (i+1))
      = (∑ i ∈ Finset.range 106, stT235 (i+1)) + stT235 107 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 106
    simpa using h
  have hprev := st235_p106
  have hstep := st235_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p108 : ((55484940756489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT235 (i+1))
      = (∑ i ∈ Finset.range 107, stT235 (i+1)) + stT235 108 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 107
    simpa using h
  have hprev := st235_p107
  have hstep := st235_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p109 : ((10905485584749/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT235 (i+1))
      = (∑ i ∈ Finset.range 108, stT235 (i+1)) + stT235 109 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 108
    simpa using h
  have hprev := st235_p108
  have hstep := st235_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p110 : ((55023994747193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT235 (i+1))
      = (∑ i ∈ Finset.range 109, stT235 (i+1)) + stT235 110 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 109
    simpa using h
  have hprev := st235_p109
  have hstep := st235_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p111 : ((27725639800677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT235 (i+1))
      = (∑ i ∈ Finset.range 110, stT235 (i+1)) + stT235 111 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 110
    simpa using h
  have hprev := st235_p110
  have hstep := st235_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p112 : ((27254311080693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT235 (i+1))
      = (∑ i ∈ Finset.range 111, stT235 (i+1)) + stT235 112 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 111
    simpa using h
  have hprev := st235_p111
  have hstep := st235_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p113 : ((27515167562733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT235 (i+1))
      = (∑ i ∈ Finset.range 112, stT235 (i+1)) + stT235 113 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 112
    simpa using h
  have hprev := st235_p112
  have hstep := st235_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p114 : ((55465417257951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT235 (i+1))
      = (∑ i ∈ Finset.range 113, stT235 (i+1)) + stT235 114 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 113
    simpa using h
  have hprev := st235_p113
  have hstep := st235_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p115 : ((27266433282603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT235 (i+1))
      = (∑ i ∈ Finset.range 114, stT235 (i+1)) + stT235 115 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 114
    simpa using h
  have hprev := st235_p114
  have hstep := st235_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p116 : ((27473456969037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT235 (i+1))
      = (∑ i ∈ Finset.range 115, stT235 (i+1)) + stT235 116 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 115
    simpa using h
  have hprev := st235_p115
  have hstep := st235_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p117 : ((27757619147287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT235 (i+1))
      = (∑ i ∈ Finset.range 116, stT235 (i+1)) + stT235 117 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 116
    simpa using h
  have hprev := st235_p116
  have hstep := st235_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p118 : ((27309735474837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT235 (i+1))
      = (∑ i ∈ Finset.range 117, stT235 (i+1)) + stT235 118 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 117
    simpa using h
  have hprev := st235_p117
  have hstep := st235_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p119 : ((13695755447487/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT235 (i+1))
      = (∑ i ∈ Finset.range 118, stT235 (i+1)) + stT235 119 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 118
    simpa using h
  have hprev := st235_p118
  have hstep := st235_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p120 : ((27774480399549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT235 (i+1))
      = (∑ i ∈ Finset.range 119, stT235 (i+1)) + stT235 120 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 119
    simpa using h
  have hprev := st235_p119
  have hstep := st235_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p121 : ((10961404326799/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT235 (i+1))
      = (∑ i ∈ Finset.range 120, stT235 (i+1)) + stT235 121 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 120
    simpa using h
  have hprev := st235_p120
  have hstep := st235_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p122 : ((2183220404639/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT235 (i+1))
      = (∑ i ∈ Finset.range 121, stT235 (i+1)) + stT235 122 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 121
    simpa using h
  have hprev := st235_p121
  have hstep := st235_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p123 : ((55478089145391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT235 (i+1))
      = (∑ i ∈ Finset.range 122, stT235 (i+1)) + stT235 123 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 122
    simpa using h
  have hprev := st235_p122
  have hstep := st235_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p124 : ((55106296987121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT235 (i+1))
      = (∑ i ∈ Finset.range 123, stT235 (i+1)) + stT235 124 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 123
    simpa using h
  have hprev := st235_p123
  have hstep := st235_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p125 : ((54447903169753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT235 (i+1))
      = (∑ i ∈ Finset.range 124, stT235 (i+1)) + stT235 125 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 124
    simpa using h
  have hprev := st235_p124
  have hstep := st235_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p126 : ((55218528882373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT235 (i+1))
      = (∑ i ∈ Finset.range 125, stT235 (i+1)) + stT235 126 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 125
    simpa using h
  have hprev := st235_p125
  have hstep := st235_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p127 : ((55428198682189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT235 (i+1))
      = (∑ i ∈ Finset.range 126, stT235 (i+1)) + stT235 127 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 126
    simpa using h
  have hprev := st235_p126
  have hstep := st235_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p128 : ((54544774301869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT235 (i+1))
      = (∑ i ∈ Finset.range 127, stT235 (i+1)) + stT235 128 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 127
    simpa using h
  have hprev := st235_p127
  have hstep := st235_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p129 : ((54798000526369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT235 (i+1))
      = (∑ i ∈ Finset.range 128, stT235 (i+1)) + stT235 129 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 128
    simpa using h
  have hprev := st235_p128
  have hstep := st235_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p130 : ((55552168667641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT235 (i+1))
      = (∑ i ∈ Finset.range 129, stT235 (i+1)) + stT235 130 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 129
    simpa using h
  have hprev := st235_p129
  have hstep := st235_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p131 : ((54946647417391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT235 (i+1))
      = (∑ i ∈ Finset.range 130, stT235 (i+1)) + stT235 131 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 130
    simpa using h
  have hprev := st235_p130
  have hstep := st235_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p132 : ((13615792892293/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT235 (i+1))
      = (∑ i ∈ Finset.range 131, stT235 (i+1)) + stT235 132 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 131
    simpa using h
  have hprev := st235_p131
  have hstep := st235_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p133 : ((55266413655777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT235 (i+1))
      = (∑ i ∈ Finset.range 132, stT235 (i+1)) + stT235 133 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 132
    simpa using h
  have hprev := st235_p132
  have hstep := st235_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p134 : ((55435087338249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT235 (i+1))
      = (∑ i ∈ Finset.range 133, stT235 (i+1)) + stT235 134 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 133
    simpa using h
  have hprev := st235_p133
  have hstep := st235_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p135 : ((6821819502461/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT235 (i+1))
      = (∑ i ∈ Finset.range 134, stT235 (i+1)) + stT235 135 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 134
    simpa using h
  have hprev := st235_p134
  have hstep := st235_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p136 : ((54697036747/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT235 (i+1))
      = (∑ i ∈ Finset.range 135, stT235 (i+1)) + stT235 136 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 135
    simpa using h
  have hprev := st235_p135
  have hstep := st235_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p137 : ((2775731965443/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT235 (i+1))
      = (∑ i ∈ Finset.range 136, stT235 (i+1)) + stT235 137 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 136
    simpa using h
  have hprev := st235_p136
  have hstep := st235_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p138 : ((27578898741001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT235 (i+1))
      = (∑ i ∈ Finset.range 137, stT235 (i+1)) + stT235 138 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 137
    simpa using h
  have hprev := st235_p137
  have hstep := st235_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p139 : ((6804804564557/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT235 (i+1))
      = (∑ i ∈ Finset.range 138, stT235 (i+1)) + stT235 139 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 138
    simpa using h
  have hprev := st235_p138
  have hstep := st235_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p140 : ((27482364985091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT235 (i+1))
      = (∑ i ∈ Finset.range 139, stT235 (i+1)) + stT235 140 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 139
    simpa using h
  have hprev := st235_p139
  have hstep := st235_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p141 : ((55566885620353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT235 (i+1))
      = (∑ i ∈ Finset.range 140, stT235 (i+1)) + stT235 141 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 140
    simpa using h
  have hprev := st235_p140
  have hstep := st235_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p142 : ((10985730996251/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT235 (i+1))
      = (∑ i ∈ Finset.range 141, stT235 (i+1)) + stT235 142 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 141
    simpa using h
  have hprev := st235_p141
  have hstep := st235_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p143 : ((54437032739013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT235 (i+1))
      = (∑ i ∈ Finset.range 142, stT235 (i+1)) + stT235 143 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 142
    simpa using h
  have hprev := st235_p142
  have hstep := st235_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p144 : ((55142342456889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT235 (i+1))
      = (∑ i ∈ Finset.range 143, stT235 (i+1)) + stT235 144 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 143
    simpa using h
  have hprev := st235_p143
  have hstep := st235_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p145 : ((55544840257977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT235 (i+1))
      = (∑ i ∈ Finset.range 144, stT235 (i+1)) + stT235 145 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 144
    simpa using h
  have hprev := st235_p144
  have hstep := st235_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p146 : ((2192153993869/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT235 (i+1))
      = (∑ i ∈ Finset.range 145, stT235 (i+1)) + stT235 146 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 145
    simpa using h
  have hprev := st235_p145
  have hstep := st235_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p147 : ((54461164044817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT235 (i+1))
      = (∑ i ∈ Finset.range 146, stT235 (i+1)) + stT235 147 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 146
    simpa using h
  have hprev := st235_p146
  have hstep := st235_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p148 : ((55216299518839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT235 (i+1))
      = (∑ i ∈ Finset.range 147, stT235 (i+1)) + stT235 148 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 147
    simpa using h
  have hprev := st235_p147
  have hstep := st235_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p149 : ((55530953038243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT235 (i+1))
      = (∑ i ∈ Finset.range 148, stT235 (i+1)) + stT235 149 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 148
    simpa using h
  have hprev := st235_p148
  have hstep := st235_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p150 : ((54776715567487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT235 (i+1))
      = (∑ i ∈ Finset.range 149, stT235 (i+1)) + stT235 150 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 149
    simpa using h
  have hprev := st235_p149
  have hstep := st235_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p151 : ((54457905588847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT235 (i+1))
      = (∑ i ∈ Finset.range 150, stT235 (i+1)) + stT235 151 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 150
    simpa using h
  have hprev := st235_p150
  have hstep := st235_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p152 : ((55197774683251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT235 (i+1))
      = (∑ i ∈ Finset.range 151, stT235 (i+1)) + stT235 152 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 151
    simpa using h
  have hprev := st235_p151
  have hstep := st235_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p153 : ((55550786057503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT235 (i+1))
      = (∑ i ∈ Finset.range 152, stT235 (i+1)) + stT235 153 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 152
    simpa using h
  have hprev := st235_p152
  have hstep := st235_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p154 : ((54840414403499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT235 (i+1))
      = (∑ i ∈ Finset.range 153, stT235 (i+1)) + stT235 154 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 153
    simpa using h
  have hprev := st235_p153
  have hstep := st235_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p155 : ((54426356903159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT235 (i+1))
      = (∑ i ∈ Finset.range 154, stT235 (i+1)) + stT235 155 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 154
    simpa using h
  have hprev := st235_p154
  have hstep := st235_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p156 : ((55086631900919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT235 (i+1))
      = (∑ i ∈ Finset.range 155, stT235 (i+1)) + stT235 156 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 155
    simpa using h
  have hprev := st235_p155
  have hstep := st235_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p157 : ((55582353442787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT235 (i+1))
      = (∑ i ∈ Finset.range 156, stT235 (i+1)) + stT235 157 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 156
    simpa using h
  have hprev := st235_p156
  have hstep := st235_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p158 : ((54999666079079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT235 (i+1))
      = (∑ i ∈ Finset.range 157, stT235 (i+1)) + stT235 158 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 157
    simpa using h
  have hprev := st235_p157
  have hstep := st235_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p159 : ((10882121851787/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT235 (i+1))
      = (∑ i ∈ Finset.range 158, stT235 (i+1)) + stT235 159 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 158
    simpa using h
  have hprev := st235_p158
  have hstep := st235_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p160 : ((13720074935377/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT235 (i+1))
      = (∑ i ∈ Finset.range 159, stT235 (i+1)) + stT235 160 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 159
    simpa using h
  have hprev := st235_p159
  have hstep := st235_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p161 : ((27780203179499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT235 (i+1))
      = (∑ i ∈ Finset.range 160, stT235 (i+1)) + stT235 161 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 160
    simpa using h
  have hprev := st235_p160
  have hstep := st235_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p162 : ((55244364661873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT235 (i+1))
      = (∑ i ∈ Finset.range 161, stT235 (i+1)) + stT235 162 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 161
    simpa using h
  have hprev := st235_p161
  have hstep := st235_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p163 : ((27246806454839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT235 (i+1))
      = (∑ i ∈ Finset.range 162, stT235 (i+1)) + stT235 163 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 162
    simpa using h
  have hprev := st235_p162
  have hstep := st235_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p164 : ((27307372919523/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT235 (i+1))
      = (∑ i ∈ Finset.range 163, stT235 (i+1)) + stT235 164 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 163
    simpa using h
  have hprev := st235_p163
  have hstep := st235_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p165 : ((5539313329233/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT235 (i+1))
      = (∑ i ∈ Finset.range 164, stT235 (i+1)) + stT235 165 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 164
    simpa using h
  have hprev := st235_p164
  have hstep := st235_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p166 : ((173435348089/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT235 (i+1))
      = (∑ i ∈ Finset.range 165, stT235 (i+1)) + stT235 166 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 165
    simpa using h
  have hprev := st235_p165
  have hstep := st235_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p167 : ((427806617251/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT235 (i+1))
      = (∑ i ∈ Finset.range 166, stT235 (i+1)) + stT235 167 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 166
    simpa using h
  have hprev := st235_p166
  have hstep := st235_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p168 : ((54413609706679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT235 (i+1))
      = (∑ i ∈ Finset.range 167, stT235 (i+1)) + stT235 168 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 167
    simpa using h
  have hprev := st235_p167
  have hstep := st235_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p169 : ((55030298320759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT235 (i+1))
      = (∑ i ∈ Finset.range 168, stT235 (i+1)) + stT235 169 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 168
    simpa using h
  have hprev := st235_p168
  have hstep := st235_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p170 : ((55593607301983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT235 (i+1))
      = (∑ i ∈ Finset.range 169, stT235 (i+1)) + stT235 170 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 169
    simpa using h
  have hprev := st235_p169
  have hstep := st235_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p171 : ((55191680411343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT235 (i+1))
      = (∑ i ∈ Finset.range 170, stT235 (i+1)) + stT235 171 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 170
    simpa using h
  have hprev := st235_p170
  have hstep := st235_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p172 : ((13619028760757/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT235 (i+1))
      = (∑ i ∈ Finset.range 171, stT235 (i+1)) + stT235 172 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 171
    simpa using h
  have hprev := st235_p171
  have hstep := st235_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p173 : ((54585431101183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT235 (i+1))
      = (∑ i ∈ Finset.range 172, stT235 (i+1)) + stT235 173 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 172
    simpa using h
  have hprev := st235_p172
  have hstep := st235_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p174 : ((55341527722463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT235 (i+1))
      = (∑ i ∈ Finset.range 173, stT235 (i+1)) + stT235 174 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 173
    simpa using h
  have hprev := st235_p173
  have hstep := st235_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p175 : ((11112409256539/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT235 (i+1))
      = (∑ i ∈ Finset.range 174, stT235 (i+1)) + stT235 175 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 174
    simpa using h
  have hprev := st235_p174
  have hstep := st235_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p176 : ((54910821930761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT235 (i+1))
      = (∑ i ∈ Finset.range 175, stT235 (i+1)) + stT235 176 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 175
    simpa using h
  have hprev := st235_p175
  have hstep := st235_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p177 : ((54389063159123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT235 (i+1))
      = (∑ i ∈ Finset.range 176, stT235 (i+1)) + stT235 177 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 176
    simpa using h
  have hprev := st235_p176
  have hstep := st235_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p178 : ((13696277897967/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT235 (i+1))
      = (∑ i ∈ Finset.range 177, stT235 (i+1)) + stT235 178 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 177
    simpa using h
  have hprev := st235_p177
  have hstep := st235_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p179 : ((55498568944203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT235 (i+1))
      = (∑ i ∈ Finset.range 178, stT235 (i+1)) + stT235 179 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 178
    simpa using h
  have hprev := st235_p178
  have hstep := st235_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p180 : ((55468054814919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT235 (i+1))
      = (∑ i ∈ Finset.range 179, stT235 (i+1)) + stT235 180 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 179
    simpa using h
  have hprev := st235_p179
  have hstep := st235_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p181 : ((54743950205229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT235 (i+1))
      = (∑ i ∈ Finset.range 180, stT235 (i+1)) + stT235 181 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 180
    simpa using h
  have hprev := st235_p180
  have hstep := st235_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p182 : ((54385947210229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT235 (i+1))
      = (∑ i ∈ Finset.range 181, stT235 (i+1)) + stT235 182 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 181
    simpa using h
  have hprev := st235_p181
  have hstep := st235_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p183 : ((54907726353079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT235 (i+1))
      = (∑ i ∈ Finset.range 182, stT235 (i+1)) + stT235 183 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 182
    simpa using h
  have hprev := st235_p182
  have hstep := st235_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p184 : ((13889229071131/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT235 (i+1))
      = (∑ i ∈ Finset.range 183, stT235 (i+1)) + stT235 184 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 183
    simpa using h
  have hprev := st235_p183
  have hstep := st235_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p185 : ((55413351586689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT235 (i+1))
      = (∑ i ∈ Finset.range 184, stT235 (i+1)) + stT235 185 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 184
    simpa using h
  have hprev := st235_p184
  have hstep := st235_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p186 : ((54684309696609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT235 (i+1))
      = (∑ i ∈ Finset.range 185, stT235 (i+1)) + stT235 186 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 185
    simpa using h
  have hprev := st235_p185
  have hstep := st235_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p187 : ((54387288542199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT235 (i+1))
      = (∑ i ∈ Finset.range 186, stT235 (i+1)) + stT235 187 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 186
    simpa using h
  have hprev := st235_p186
  have hstep := st235_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p188 : ((54927956844471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT235 (i+1))
      = (∑ i ∈ Finset.range 187, stT235 (i+1)) + stT235 188 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 187
    simpa using h
  have hprev := st235_p187
  have hstep := st235_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p189 : ((55562383782519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT235 (i+1))
      = (∑ i ∈ Finset.range 188, stT235 (i+1)) + stT235 189 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 188
    simpa using h
  have hprev := st235_p188
  have hstep := st235_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p190 : ((55432236110627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT235 (i+1))
      = (∑ i ∈ Finset.range 189, stT235 (i+1)) + stT235 190 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 189
    simpa using h
  have hprev := st235_p189
  have hstep := st235_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p191 : ((54717508985727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT235 (i+1))
      = (∑ i ∈ Finset.range 190, stT235 (i+1)) + stT235 191 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 190
    simpa using h
  have hprev := st235_p190
  have hstep := st235_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p192 : ((54371151428951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT235 (i+1))
      = (∑ i ∈ Finset.range 191, stT235 (i+1)) + stT235 192 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 191
    simpa using h
  have hprev := st235_p191
  have hstep := st235_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p193 : ((54845892455531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT235 (i+1))
      = (∑ i ∈ Finset.range 192, stT235 (i+1)) + stT235 193 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 192
    simpa using h
  have hprev := st235_p192
  have hstep := st235_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p194 : ((55516787590673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT235 (i+1))
      = (∑ i ∈ Finset.range 193, stT235 (i+1)) + stT235 194 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 193
    simpa using h
  have hprev := st235_p193
  have hstep := st235_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p195 : ((27757882131169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT235 (i+1))
      = (∑ i ∈ Finset.range 194, stT235 (i+1)) + stT235 195 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 194
    simpa using h
  have hprev := st235_p194
  have hstep := st235_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p196 : ((27424551283551/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT235 (i+1))
      = (∑ i ∈ Finset.range 195, stT235 (i+1)) + stT235 196 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 195
    simpa using h
  have hprev := st235_p195
  have hstep := st235_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p197 : ((27183743210261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT235 (i+1))
      = (∑ i ∈ Finset.range 196, stT235 (i+1)) + stT235 197 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 196
    simpa using h
  have hprev := st235_p196
  have hstep := st235_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p198 : ((10935012366343/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT235 (i+1))
      = (∑ i ∈ Finset.range 197, stT235 (i+1)) + stT235 198 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 197
    simpa using h
  have hprev := st235_p197
  have hstep := st235_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p199 : ((55382600211101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT235 (i+1))
      = (∑ i ∈ Finset.range 198, stT235 (i+1)) + stT235 199 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 198
    simpa using h
  have hprev := st235_p198
  have hstep := st235_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p200 : ((55613116767101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT235 (i+1))
      = (∑ i ∈ Finset.range 199, stT235 (i+1)) + stT235 200 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 199
    simpa using h
  have hprev := st235_p199
  have hstep := st235_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p201 : ((55087867466627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT235 (i+1))
      = (∑ i ∈ Finset.range 200, stT235 (i+1)) + stT235 201 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 200
    simpa using h
  have hprev := st235_p200
  have hstep := st235_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p202 : ((54449879276529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT235 (i+1))
      = (∑ i ∈ Finset.range 201, stT235 (i+1)) + stT235 202 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 201
    simpa using h
  have hprev := st235_p201
  have hstep := st235_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p203 : ((10893492605043/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT235 (i+1))
      = (∑ i ∈ Finset.range 202, stT235 (i+1)) + stT235 203 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 202
    simpa using h
  have hprev := st235_p202
  have hstep := st235_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p204 : ((11022950731491/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT235 (i+1))
      = (∑ i ∈ Finset.range 203, stT235 (i+1)) + stT235 204 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 203
    simpa using h
  have hprev := st235_p203
  have hstep := st235_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p205 : ((11124361510317/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT235 (i+1))
      = (∑ i ∈ Finset.range 204, stT235 (i+1)) + stT235 205 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 204
    simpa using h
  have hprev := st235_p204
  have hstep := st235_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p206 : ((55395335558353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT235 (i+1))
      = (∑ i ∈ Finset.range 205, stT235 (i+1)) + stT235 206 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 205
    simpa using h
  have hprev := st235_p205
  have hstep := st235_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p207 : ((27351924342239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT235 (i+1))
      = (∑ i ∈ Finset.range 206, stT235 (i+1)) + stT235 207 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 206
    simpa using h
  have hprev := st235_p206
  have hstep := st235_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p208 : ((27173651478943/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT235 (i+1))
      = (∑ i ∈ Finset.range 207, stT235 (i+1)) + stT235 208 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 207
    simpa using h
  have hprev := st235_p207
  have hstep := st235_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p209 : ((13682606512409/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT235 (i+1))
      = (∑ i ∈ Finset.range 208, stT235 (i+1)) + stT235 209 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 208
    simpa using h
  have hprev := st235_p208
  have hstep := st235_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p210 : ((55413896098431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT235 (i+1))
      = (∑ i ∈ Finset.range 209, stT235 (i+1)) + stT235 210 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 209
    simpa using h
  have hprev := st235_p209
  have hstep := st235_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p211 : ((11125613622903/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT235 (i+1))
      = (∑ i ∈ Finset.range 210, stT235 (i+1)) + stT235 211 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 210
    simpa using h
  have hprev := st235_p210
  have hstep := st235_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p212 : ((55137895439809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT235 (i+1))
      = (∑ i ∈ Finset.range 211, stT235 (i+1)) + stT235 212 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 211
    simpa using h
  have hprev := st235_p211
  have hstep := st235_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p213 : ((2724479816519/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT235 (i+1))
      = (∑ i ∈ Finset.range 212, stT235 (i+1)) + stT235 213 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 212
    simpa using h
  have hprev := st235_p212
  have hstep := st235_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p214 : ((6799246869191/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT235 (i+1))
      = (∑ i ∈ Finset.range 213, stT235 (i+1)) + stT235 214 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 213
    simpa using h
  have hprev := st235_p213
  have hstep := st235_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p215 : ((6868846402873/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT235 (i+1))
      = (∑ i ∈ Finset.range 214, stT235 (i+1)) + stT235 215 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 214
    simpa using h
  have hprev := st235_p214
  have hstep := st235_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p216 : ((27777915602443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT235 (i+1))
      = (∑ i ∈ Finset.range 215, stT235 (i+1)) + stT235 216 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 215
    simpa using h
  have hprev := st235_p215
  have hstep := st235_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p217 : ((27781421492281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT235 (i+1))
      = (∑ i ∈ Finset.range 216, stT235 (i+1)) + stT235 217 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 216
    simpa using h
  have hprev := st235_p216
  have hstep := st235_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p218 : ((13742166856727/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT235 (i+1))
      = (∑ i ∈ Finset.range 217, stT235 (i+1)) + stT235 218 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 217
    simpa using h
  have hprev := st235_p217
  have hstep := st235_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p219 : ((1360037235989/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT235 (i+1))
      = (∑ i ∈ Finset.range 218, stT235 (i+1)) + stT235 219 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 218
    simpa using h
  have hprev := st235_p218
  have hstep := st235_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p220 : ((27225860655127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT235 (i+1))
      = (∑ i ∈ Finset.range 219, stT235 (i+1)) + stT235 220 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 219
    simpa using h
  have hprev := st235_p219
  have hstep := st235_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p221 : ((27531505658791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT235 (i+1))
      = (∑ i ∈ Finset.range 220, stT235 (i+1)) + stT235 221 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 220
    simpa using h
  have hprev := st235_p220
  have hstep := st235_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p222 : ((27802539928583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT235 (i+1))
      = (∑ i ∈ Finset.range 221, stT235 (i+1)) + stT235 222 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 221
    simpa using h
  have hprev := st235_p221
  have hstep := st235_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p223 : ((27763797327833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT235 (i+1))
      = (∑ i ∈ Finset.range 222, stT235 (i+1)) + stT235 223 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 222
    simpa using h
  have hprev := st235_p222
  have hstep := st235_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p224 : ((13728260827579/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT235 (i+1))
      = (∑ i ∈ Finset.range 223, stT235 (i+1)) + stT235 224 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 223
    simpa using h
  have hprev := st235_p223
  have hstep := st235_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p225 : ((27189811521803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT235 (i+1))
      = (∑ i ∈ Finset.range 224, stT235 (i+1)) + stT235 225 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 224
    simpa using h
  have hprev := st235_p224
  have hstep := st235_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p226 : ((27227857063853/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT235 (i+1))
      = (∑ i ∈ Finset.range 225, stT235 (i+1)) + stT235 226 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 225
    simpa using h
  have hprev := st235_p225
  have hstep := st235_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p227 : ((13765526515603/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT235 (i+1))
      = (∑ i ∈ Finset.range 226, stT235 (i+1)) + stT235 227 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 226
    simpa using h
  have hprev := st235_p226
  have hstep := st235_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p228 : ((27801612202649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT235 (i+1))
      = (∑ i ∈ Finset.range 227, stT235 (i+1)) + stT235 228 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 227
    simpa using h
  have hprev := st235_p227
  have hstep := st235_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p229 : ((55555617022081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT235 (i+1))
      = (∑ i ∈ Finset.range 228, stT235 (i+1)) + stT235 229 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 228
    simpa using h
  have hprev := st235_p228
  have hstep := st235_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p230 : ((6871141736067/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT235 (i+1))
      = (∑ i ∈ Finset.range 229, stT235 (i+1)) + stT235 230 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 229
    simpa using h
  have hprev := st235_p229
  have hstep := st235_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p231 : ((1360159556983/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT235 (i+1))
      = (∑ i ∈ Finset.range 230, stT235 (i+1)) + stT235 231 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 230
    simpa using h
  have hprev := st235_p230
  have hstep := st235_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p232 : ((6799895708573/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT235 (i+1))
      = (∑ i ∈ Finset.range 231, stT235 (i+1)) + stT235 232 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 231
    simpa using h
  have hprev := st235_p231
  have hstep := st235_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p233 : ((27475166689273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT235 (i+1))
      = (∑ i ∈ Finset.range 232, stT235 (i+1)) + stT235 233 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 232
    simpa using h
  have hprev := st235_p232
  have hstep := st235_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p234 : ((27771507117353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT235 (i+1))
      = (∑ i ∈ Finset.range 233, stT235 (i+1)) + stT235 234 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 233
    simpa using h
  have hprev := st235_p233
  have hstep := st235_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p235 : ((27814809954649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT235 (i+1))
      = (∑ i ∈ Finset.range 234, stT235 (i+1)) + stT235 235 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 234
    simpa using h
  have hprev := st235_p234
  have hstep := st235_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p236 : ((55134294377613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT235 (i+1))
      = (∑ i ∈ Finset.range 235, stT235 (i+1)) + stT235 236 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 235
    simpa using h
  have hprev := st235_p235
  have hstep := st235_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p237 : ((54511358046753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT235 (i+1))
      = (∑ i ∈ Finset.range 236, stT235 (i+1)) + stT235 237 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 236
    simpa using h
  have hprev := st235_p236
  have hstep := st235_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p238 : ((54323610295581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT235 (i+1))
      = (∑ i ∈ Finset.range 237, stT235 (i+1)) + stT235 238 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 237
    simpa using h
  have hprev := st235_p237
  have hstep := st235_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p239 : ((54736081997017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT235 (i+1))
      = (∑ i ∈ Finset.range 238, stT235 (i+1)) + stT235 239 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 238
    simpa using h
  have hprev := st235_p238
  have hstep := st235_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p240 : ((27689097328123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT235 (i+1))
      = (∑ i ∈ Finset.range 239, stT235 (i+1)) + stT235 240 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 239
    simpa using h
  have hprev := st235_p239
  have hstep := st235_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p241 : ((27841146164909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT235 (i+1))
      = (∑ i ∈ Finset.range 240, stT235 (i+1)) + stT235 241 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 240
    simpa using h
  have hprev := st235_p240
  have hstep := st235_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p242 : ((27692316749609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT235 (i+1))
      = (∑ i ∈ Finset.range 241, stT235 (i+1)) + stT235 242 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 241
    simpa using h
  have hprev := st235_p241
  have hstep := st235_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p243 : ((27373870521201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT235 (i+1))
      = (∑ i ∈ Finset.range 242, stT235 (i+1)) + stT235 243 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 242
    simpa using h
  have hprev := st235_p242
  have hstep := st235_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p244 : ((27161338063791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT235 (i+1))
      = (∑ i ∈ Finset.range 243, stT235 (i+1)) + stT235 244 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 243
    simpa using h
  have hprev := st235_p243
  have hstep := st235_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p245 : ((5447145629271/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT235 (i+1))
      = (∑ i ∈ Finset.range 244, stT235 (i+1)) + stT235 245 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 244
    simpa using h
  have hprev := st235_p244
  have hstep := st235_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p246 : ((5506387916039/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT235 (i+1))
      = (∑ i ∈ Finset.range 245, stT235 (i+1)) + stT235 246 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 245
    simpa using h
  have hprev := st235_p245
  have hstep := st235_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p247 : ((5559785505603/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT235 (i+1))
      = (∑ i ∈ Finset.range 246, stT235 (i+1)) + stT235 247 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 246
    simpa using h
  have hprev := st235_p246
  have hstep := st235_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p248 : ((5562729365603/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT235 (i+1))
      = (∑ i ∈ Finset.range 247, stT235 (i+1)) + stT235 248 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 247
    simpa using h
  have hprev := st235_p247
  have hstep := st235_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p249 : ((11026229690471/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT235 (i+1))
      = (∑ i ∈ Finset.range 248, stT235 (i+1)) + stT235 249 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 248
    simpa using h
  have hprev := st235_p248
  have hstep := st235_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_p250 : ((54521632263931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT235 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT235 (i+1))
      = (∑ i ∈ Finset.range 249, stT235 (i+1)) + stT235 250 := by
    have h := Finset.sum_range_succ (fun i => stT235 (i+1)) 249
    simpa using h
  have hprev := st235_p249
  have hstep := st235_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st235_s250 :
    |Real.sin (((235 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))
      - ((-267063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -7178121/10000000) (δ := 2363/200000000) (ψ := -204787/1000000) 235 207
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 235`** (evaluated boundary). -/
theorem station_235_sign : 0 < hardyG ((((235:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 235 250 (by norm_num) (by norm_num)
    ((-204787/1000000 : ℚ) : ℝ)
  have hchain := st235_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT235 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((235 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-204787/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st235_c250
  have hsinb := abs_le.mp st235_s250
  have hbdy_lo : ((15996018845849/883604000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((235 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ))) / 2
          - ((((235:ℕ)):ℝ))
            * Real.sin (((235 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-204787/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((235:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((235:ℝ) * Real.log (250:ℝ) - ((-204787/1000000 : ℚ) : ℝ))) / 2
        - ((235:ℝ)) * Real.sin ((235:ℝ) * Real.log (250:ℝ) - ((-204787/1000000 : ℚ) : ℝ))
        ≥ ((126459739/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((235:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((126459739/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((126459739/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((126459739/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((235:ℕ)):ℝ))+1) * (((((235:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((190288855031/156250000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((54521632263931/10000000000000 : ℚ) : ℝ) + ((15996018845849/883604000000000 : ℚ) : ℝ)
      - ((190288855031/156250000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-204787/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((235:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-204787/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((235:ℕ)):ℝ)))).re
      - Real.sin ((-204787/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((235:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((235:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((235:ℕ)):ℝ))
      = (((((235:ℕ)):ℝ)) * (Real.log ((((235:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((235:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_235
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
  have hθwin : |(((-204787/1000000 : ℚ) : ℝ) + ((49:ℤ)) * (2*Real.pi)) - theta ((((235:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((235:ℕ)):ℝ)))
    (φ := ((-204787/1000000 : ℚ) : ℝ) + ((49:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-204787/1000000 : ℚ)) : ℝ) 49).1,
    (cos_sin_shift (((-204787/1000000 : ℚ)) : ℝ) 49).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_235_sign
end AxiomAudit
