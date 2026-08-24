import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 307` (rung-309; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT307 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((307 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((56493/500000 : ℚ) : ℝ))

theorem st307_c1 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((124203/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56493/2000000) (δ := 1/1000000000) (ψ := 56493/500000) 307 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t1 : ((248381/250000 : ℚ) : ℝ) ≤ stT307 1 := by
  have hc : ((248381/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((248381/250000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((248381/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c2 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((585653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1181389/5000000) (δ := 7773/500000000) (ψ := 56493/500000) 307 34
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t2 : ((4140484495051/10000000000000 : ℚ) : ℝ) ≤ stT307 2 := by
  have hc : ((585553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4140484495051/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((585553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c3 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-265693/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -266379/500000) (δ := 7757/500000000) (ψ := 56493/500000) 307 54
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t3 : ((-1534268007729/5000000000000 : ℚ) : ℝ) ≤ stT307 3 := by
  have hc : ((-265743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1534268007729/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-265743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c4 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-102481/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2221527/5000000) (δ := 15513/1000000000) (ψ := 56493/500000) 307 68
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t4 : ((-512655102531/5000000000000 : ℚ) : ℝ) ≤ stT307 4 := by
  have hc : ((-102531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512655102531/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-102531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c5 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-72867/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5967937/10000000) (δ := 7767/500000000) (ψ := 56493/500000) 307 79
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t5 : ((-40739481909/125000000000 : ℚ) : ℝ) ≤ stT307 5 := by
  have hc : ((-72877/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40739481909/125000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-72877/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c6 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-24603/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1481571/2000000) (δ := 1547/100000000) (ψ := 56493/500000) 307 88
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t6 : ((-200903070913/500000000000 : ℚ) : ℝ) ≤ stT307 6 := by
  have hc : ((-49211/50000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-200903070913/500000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-49211/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c7 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((929099/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 189413/2000000) (δ := 3871/250000000) (ψ := 56493/500000) 307 95
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t7 : ((877821374089/2500000000000 : ℚ) : ℝ) ≤ stT307 7 := by
  have hc : ((928999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((877821374089/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((928999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c8 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-430831/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6523329/10000000) (δ := 15469/1000000000) (ψ := 56493/500000) 307 102
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t8 : ((-761697212727/2500000000000 : ℚ) : ℝ) ≤ stT307 8 := by
  have hc : ((-430881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-761697212727/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-430881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c9 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-267001/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5335307/10000000) (δ := 15533/1000000000) (ψ := 56493/500000) 307 107
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t9 : ((-445085089017/2500000000000 : ℚ) : ℝ) ≤ stT307 9 := by
  have hc : ((-267051/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-445085089017/2500000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-267051/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c10 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-996981/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 306387/400000) (δ := 7703/500000000) (ψ := 56493/500000) 307 112
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t10 : ((-1576523655259/5000000000000 : ℚ) : ℝ) ≤ stT307 10 := by
  have hc : ((-997081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1576523655259/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-997081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c11 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((307593/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2270437/10000000) (δ := 15361/1000000000) (ψ := 56493/500000) 307 117
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t11 : ((927276897359/5000000000000 : ℚ) : ℝ) ≤ stT307 11 := by
  have hc : ((307543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((927276897359/5000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((307543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c12 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-99233/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6219833/10000000) (δ := 15533/1000000000) (ψ := 56493/500000) 307 121
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t12 : ((-17906071601/78125000000 : ℚ) : ℝ) ≤ stT307 12 := by
  have hc : ((-198491/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17906071601/78125000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-198491/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c13 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-174969/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4820753/10000000) (δ := 15499/1000000000) (ψ := 56493/500000) 307 125
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t13 : ((-485415371519/5000000000000 : ℚ) : ℝ) ≤ stT307 13 := by
  have hc : ((-175019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-485415371519/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-175019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c14 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((449507/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -113321/1000000) (δ := 1941/125000000) (ψ := 56493/500000) 307 129
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t14 : ((300306042921/1250000000000 : ℚ) : ℝ) ≤ stT307 14 := by
  have hc : ((449457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((300306042921/1250000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((449457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c15 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-37797/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4694951/10000000) (δ := 15549/1000000000) (ψ := 56493/500000) 307 132
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t15 : ((-195247426191/2500000000000 : ℚ) : ℝ) ≤ stT307 15 := by
  have hc : ((-75619/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195247426191/2500000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-75619/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c16 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-955381/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7104359/10000000) (δ := 3883/250000000) (ψ := 56493/500000) 307 135
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t16 : ((-2388703455481/10000000000000 : ℚ) : ℝ) ≤ stT307 16 := by
  have hc : ((-955481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2388703455481/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-955481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c17 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-858913/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 130197/200000) (δ := 15411/1000000000) (ψ := 56493/500000) 307 138
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t17 : ((-2083413192641/10000000000000 : ℚ) : ℝ) ≤ stT307 17 := by
  have hc : ((-859013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2083413192641/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-859013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c18 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((265559/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 406879/1250000) (δ := 15489/1000000000) (ψ := 56493/500000) 307 141
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t18 : ((312846351549/5000000000000 : ℚ) : ℝ) ≤ stT307 18 := by
  have hc : ((265459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((312846351549/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((265459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c19 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((582567/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2372281/10000000) (δ := 3107/200000000) (ψ := 56493/500000) 307 144
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t19 : ((1336270745319/10000000000000 : ℚ) : ℝ) ≤ stT307 19 := by
  have hc : ((582467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1336270745319/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((582467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c20 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-306939/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27897/50000) (δ := 309/20000000) (ψ := 56493/500000) 307 146
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t20 : ((-171612069813/1250000000000 : ℚ) : ℝ) ≤ stT307 20 := by
  have hc : ((-306989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171612069813/1250000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-306989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c21 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-13671/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1024503/2500000) (δ := 3883/250000000) (ψ := 56493/500000) 307 149
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t21 : ((-29876212689/2000000000000 : ℚ) : ℝ) ≤ stT307 21 := by
  have hc : ((-13691/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29876212689/2000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-13691/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c22 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((249277/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 95081/5000000) (δ := 7693/500000000) (ψ := 56493/500000) 307 151
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t22 : ((132851752191/625000000000 : ℚ) : ℝ) ≤ stT307 22 := by
  have hc : ((62313/62500 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132851752191/625000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((62313/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c23 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((5033/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 180687/625000) (δ := 77/5000000) (ψ := 56493/500000) 307 153
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t23 : ((5245961661/62500000000 : ℚ) : ℝ) ≤ stT307 23 := by
  have hc : ((20127/50000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5245961661/62500000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((20127/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c24 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-21231/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2069779/5000000) (δ := 15489/1000000000) (ψ := 56493/500000) 307 155
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t24 : ((-2711789997/156250000000 : ℚ) : ℝ) ≤ stT307 24 := by
  have hc : ((-2657/31250 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2711789997/156250000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-2657/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c25 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-12747/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4054517/10000000) (δ := 15429/1000000000) (ψ := 56493/500000) 307 157
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t25 : ((-6386003193/625000000000 : ℚ) : ℝ) ≤ stT307 25 := by
  have hc : ((-3193/62500 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6386003193/625000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-3193/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c26 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((456987/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1370239/5000000) (δ := 15543/1000000000) (ψ := 56493/500000) 307 159
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t26 : ((896028965807/10000000000000 : ℚ) : ℝ) ≤ stT307 26 := by
  have hc : ((456887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((896028965807/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((456887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c27 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((993269/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 290231/10000000) (δ := 7723/500000000) (ψ := 56493/500000) 307 161
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t27 : ((3822707481/20000000000 : ℚ) : ℝ) ≤ stT307 27 := by
  have hc : ((993169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3822707481/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((993169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c28 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((281543/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1606743/5000000) (δ := 15531/1000000000) (ψ := 56493/500000) 307 163
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t28 : ((265938586573/5000000000000 : ℚ) : ℝ) ≤ stT307 28 := by
  have hc : ((281443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((265938586573/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((281443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c29 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-39921/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7696839/10000000) (δ := 7743/500000000) (ψ := 56493/500000) 307 165
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t29 : ((-1482777769/8000000000 : ℚ) : ℝ) ≤ stT307 29 := by
  have hc : ((-1597/1600 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1482777769/8000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-1597/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c30 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((62647/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2614599/10000000) (δ := 15493/1000000000) (ψ := 56493/500000) 307 166
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t30 : ((228708749329/2500000000000 : ℚ) : ℝ) ≤ stT307 30 := by
  have hc : ((125269/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228708749329/2500000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((125269/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c31 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((116499/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -90877/250000) (δ := 3099/200000000) (ψ := 56493/500000) 307 168
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t31 : ((209058773147/10000000000000 : ℚ) : ℝ) ≤ stT307 31 := by
  have hc : ((116399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209058773147/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((116399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c32 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-424887/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1256021/2500000) (δ := 121/7812500) (ψ := 56493/500000) 307 169
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t32 : ((-751277994029/10000000000000 : ℚ) : ℝ) ≤ stT307 32 := by
  have hc : ((-424987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-751277994029/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-424987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c33 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((444791/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2774639/10000000) (δ := 15429/1000000000) (ψ := 56493/500000) 307 171
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t33 : ((96763427527/1250000000000 : ℚ) : ℝ) ≤ stT307 33 := by
  have hc : ((444691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96763427527/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((444691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c34 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-99841/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 177183/400000) (δ := 15367/1000000000) (ψ := 56493/500000) 307 172
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t34 : ((-85655833263/2500000000000 : ℚ) : ℝ) ≤ stT307 34 := by
  have hc : ((-99891/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85655833263/2500000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-99891/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c35 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-4983/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -947689/2000000) (δ := 15451/1000000000) (ψ := 56493/500000) 307 174
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t35 : ((-134807213677/2500000000000 : ℚ) : ℝ) ≤ stT307 35 := by
  have hc : ((-79753/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134807213677/2500000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-79753/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c36 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((222903/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1174757/10000000) (δ := 3089/200000000) (ψ := 56493/500000) 307 175
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t36 : ((92865796187/625000000000 : ℚ) : ℝ) ≤ stT307 36 := by
  have hc : ((111439/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92865796187/625000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((111439/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c37 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-171193/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3247763/5000000) (δ := 7769/500000000) (ψ := 56493/500000) 307 176
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t37 : ((-28147245987/200000000000 : ℚ) : ℝ) ≤ stT307 37 := by
  have hc : ((-171213/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28147245987/200000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-171213/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c38 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-208681/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4452557/10000000) (δ := 3881/250000000) (ψ := 56493/500000) 307 178
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t38 : ((-67737533983/2000000000000 : ℚ) : ℝ) ≤ stT307 38 := by
  have hc : ((-208781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67737533983/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-208781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c39 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((995977/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56081/2500000) (δ := 3879/250000000) (ψ := 56493/500000) 307 179
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t39 : ((1594678918437/10000000000000 : ℚ) : ℝ) ≤ stT307 39 := by
  have hc : ((995877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1594678918437/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((995877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c40 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((21289/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27993/80000) (δ := 7747/500000000) (ψ := 56493/500000) 307 180
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t40 : ((33641082657/1250000000000 : ℚ) : ℝ) ≤ stT307 40 := by
  have hc : ((42553/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33641082657/1250000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((42553/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c41 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-451413/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1685683/2500000) (δ := 15401/1000000000) (ψ := 56493/500000) 307 181
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t41 : ((-352533461347/2500000000000 : ℚ) : ℝ) ≤ stT307 41 := by
  have hc : ((-451463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-352533461347/2500000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-451463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c42 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-783649/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6178287/10000000) (δ := 121/7812500) (ψ := 56493/500000) 307 183
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t42 : ((-604675677233/5000000000000 : ℚ) : ℝ) ≤ stT307 42 := by
  have hc : ((-783749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-604675677233/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-783749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c43 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((40149/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3826591/10000000) (δ := 15423/1000000000) (ψ := 56493/500000) 307 184
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t43 : ((12214824853/2000000000000 : ℚ) : ℝ) ≤ stT307 43 := by
  have hc : ((40049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12214824853/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((40049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c44 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((145511/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1890113/10000000) (δ := 1543/100000000) (ψ := 56493/500000) 307 185
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t44 : ((54833957499/500000000000 : ℚ) : ℝ) ≤ stT307 44 := by
  have hc : ((145491/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54833957499/500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((145491/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c45 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((198041/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -175101/5000000) (δ := 15537/1000000000) (ψ := 56493/500000) 307 186
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t45 : ((295192082931/2000000000000 : ℚ) : ℝ) ≤ stT307 45 := by
  have hc : ((198021/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((295192082931/2000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((198021/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c46 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((59243/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10133/125000) (δ := 15359/1000000000) (ψ := 56493/500000) 307 187
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t46 : ((349359158793/2500000000000 : ℚ) : ℝ) ≤ stT307 46 := by
  have hc : ((236947/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((349359158793/2500000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((236947/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c47 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((399999/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 804381/5000000) (δ := 1919/125000000) (ψ := 56493/500000) 307 188
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t47 : ((583385208901/5000000000000 : ℚ) : ℝ) ≤ stT307 47 := by
  have hc : ((399949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((583385208901/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((399949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c48 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((339751/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2059283/10000000) (δ := 3089/200000000) (ψ := 56493/500000) 307 189
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t48 : ((3922527447/40000000000 : ℚ) : ℝ) ≤ stT307 48 := by
  have hc : ((339701/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3922527447/40000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((339701/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c49 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((644351/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 544139/2500000) (δ := 7683/500000000) (ψ := 56493/500000) 307 190
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t49 : ((920358295321/10000000000000 : ℚ) : ℝ) ≤ stT307 49 := by
  have hc : ((644251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((920358295321/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((644251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c50 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((704061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 987121/5000000) (δ := 15473/1000000000) (ψ := 56493/500000) 307 191
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t50 : ((995550797693/10000000000000 : ℚ) : ℝ) ≤ stT307 50 := by
  have hc : ((703961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((995550797693/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((703961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c51 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((833209/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 732387/5000000) (δ := 769/50000000) (ψ := 56493/500000) 307 192
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t51 : ((29164646763/250000000000 : ℚ) : ℝ) ≤ stT307 51 := by
  have hc : ((833109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29164646763/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((833109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c52 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((965333/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 330101/5000000) (δ := 3879/250000000) (ψ := 56493/500000) 307 193
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t52 : ((5354147451/40000000000 : ℚ) : ℝ) ≤ stT307 52 := by
  have hc : ((965233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5354147451/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((965233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c53 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((985363/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -428267/10000000) (δ := 7747/500000000) (ψ := 56493/500000) 307 194
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t53 : ((270672436623/2000000000000 : ℚ) : ℝ) ≤ stT307 53 := by
  have hc : ((985263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270672436623/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((985263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c54 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((377213/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -447511/2500000) (δ := 15401/1000000000) (ψ := 56493/500000) 307 195
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t54 : ((513253593801/5000000000000 : ℚ) : ℝ) ≤ stT307 54 := by
  have hc : ((377163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((513253593801/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((377163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c55 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((203339/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3415073/10000000) (δ := 7697/500000000) (ψ := 56493/500000) 307 196
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t55 : ((274047264361/10000000000000 : ℚ) : ℝ) ≤ stT307 55 := by
  have hc : ((203239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274047264361/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((203239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c56 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-16247/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5293837/10000000) (δ := 3879/250000000) (ψ := 56493/500000) 307 197
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t56 : ((-173721246307/2500000000000 : ℚ) : ℝ) ≤ stT307 56 := by
  have hc : ((-130001/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173721246307/2500000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-130001/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c57 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-246197/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3708679/5000000) (δ := 387/25000000) (ψ := 56493/500000) 307 198
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t57 : ((-163064582163/1250000000000 : ℚ) : ℝ) ≤ stT307 57 := by
  have hc : ((-123111/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163064582163/1250000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-123111/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c58 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-71843/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5930849/10000000) (δ := 15423/1000000000) (ψ := 56493/500000) 307 198
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t58 : ((-18869531889/200000000000 : ℚ) : ℝ) ≤ stT307 58 := by
  have hc : ((-71853/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18869531889/200000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-71853/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c59 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((231541/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1671419/5000000) (δ := 1553/100000000) (ψ := 56493/500000) 307 199
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t59 : ((301310492049/10000000000000 : ℚ) : ℝ) ≤ stT307 59 := by
  have hc : ((231441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((301310492049/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((231441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c60 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((977247/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 133581/2500000) (δ := 15537/1000000000) (ψ := 56493/500000) 307 200
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t60 : ((630745457059/5000000000000 : ℚ) : ℝ) ≤ stT307 60 := by
  have hc : ((977147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((630745457059/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((977147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c61 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((68067/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1243701/5000000) (δ := 7679/500000000) (ψ := 56493/500000) 307 201
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t61 : ((10891850507/156250000000 : ℚ) : ℝ) ≤ stT307 61 := by
  have hc : ((136109/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10891850507/156250000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((136109/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c62 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-327951/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -714429/1250000) (δ := 15551/1000000000) (ψ := 56493/500000) 307 202
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t62 : ((-208280963001/2500000000000 : ℚ) : ℝ) ≤ stT307 62 := by
  have hc : ((-328001/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-208280963001/2500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-328001/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c63 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-108747/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 52519/80000) (δ := 15551/1000000000) (ψ := 56493/500000) 307 202
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t63 : ((-137024136379/1250000000000 : ℚ) : ℝ) ≤ stT307 63 := by
  have hc : ((-217519/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137024136379/1250000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-217519/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c64 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((191621/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 735933/2500000) (δ := 1943/125000000) (ψ := 56493/500000) 307 203
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t64 : ((191571/4000000 : ℚ) : ℝ) ≤ stT307 64 := by
  have hc : ((191571/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191571/4000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((191571/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c65 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((94077/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -864757/10000000) (δ := 7733/500000000) (ψ := 56493/500000) 307 204
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t65 : ((116675721249/1000000000000 : ℚ) : ℝ) ≤ stT307 65 := by
  have hc : ((94067/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116675721249/1000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((94067/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c66 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-72541/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2427457/5000000) (δ := 15473/1000000000) (ψ := 56493/500000) 307 205
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t66 : ((-17863284663/400000000000 : ℚ) : ℝ) ≤ stT307 66 := by
  have hc : ((-72561/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17863284663/400000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-72561/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c67 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-446479/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3343337/5000000) (δ := 15373/1000000000) (ψ := 56493/500000) 307 205
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t67 : ((-109104449331/1000000000000 : ℚ) : ℝ) ≤ stT307 67 := by
  have hc : ((-446529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109104449331/1000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-446529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c68 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((295007/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23493/100000) (δ := 769/50000000) (ψ := 56493/500000) 307 206
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t68 : ((178843932423/2500000000000 : ℚ) : ℝ) ≤ stT307 68 := by
  have hc : ((294957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178843932423/2500000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((294957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c69 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((651199/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -538521/2500000) (δ := 121/7812500) (ψ := 56493/500000) 307 207
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t69 : ((391915369971/5000000000000 : ℚ) : ℝ) ≤ stT307 69 := by
  have hc : ((651099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((391915369971/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((651099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c70 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-915477/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42617/62500) (δ := 3099/200000000) (ψ := 56493/500000) 307 208
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t70 : ((-1094324182133/10000000000000 : ℚ) : ℝ) ≤ stT307 70 := by
  have hc : ((-915577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1094324182133/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-915577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c71 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-28179/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 101699/250000) (δ := 963/62500000) (ψ := 56493/500000) 307 208
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t71 : ((-16750834539/2500000000000 : ℚ) : ℝ) ≤ stT307 71 := by
  have hc : ((-28229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16750834539/2500000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-28229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c72 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((935117/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -452759/5000000) (δ := 15401/1000000000) (ψ := 56493/500000) 307 209
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t72 : ((1101927819687/10000000000000 : ℚ) : ℝ) ≤ stT307 72 := by
  have hc : ((935017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1101927819687/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((935017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c73 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-372339/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6027123/10000000) (δ := 15509/1000000000) (ψ := 56493/500000) 307 210
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t73 : ((-108962138567/1250000000000 : ℚ) : ℝ) ≤ stT307 73 := by
  have hc : ((-372389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108962138567/1250000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-372389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c74 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-38807/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 176607/400000) (δ := 15509/1000000000) (ψ := 56493/500000) 307 210
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t74 : ((-45135494479/2000000000000 : ℚ) : ℝ) ≤ stT307 74 := by
  have hc : ((-38827/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45135494479/2000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-38827/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c75 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((36901/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -990559/10000000) (δ := 3879/250000000) (ψ := 56493/500000) 307 211
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t75 : ((426049659/4000000000 : ℚ) : ℝ) ≤ stT307 75 := by
  have hc : ((36897/40000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((426049659/4000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((36897/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c76 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-172717/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -204151/312500) (δ := 15479/1000000000) (ψ := 56493/500000) 307 212
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t76 : ((-198142985223/2000000000000 : ℚ) : ℝ) ≤ stT307 76 := by
  have hc : ((-172737/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198142985223/2000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-172737/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c77 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((33993/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 700001/2000000) (δ := 15379/1000000000) (ψ := 56493/500000) 307 212
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t77 : ((7743160133/400000000000 : ℚ) : ℝ) ≤ stT307 77 := by
  have hc : ((33973/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7743160133/400000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((33973/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c78 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((151089/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2304599/10000000) (δ := 967/62500000) (ψ := 56493/500000) 307 213
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t78 : ((21380786591/312500000000 : ℚ) : ℝ) ≤ stT307 78 := by
  have hc : ((18883/31250 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21380786591/312500000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((18883/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c79 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-197677/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 934073/1250000) (δ := 15431/1000000000) (ψ := 56493/500000) 307 213
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t79 : ((-6950828823/62500000000 : ℚ) : ℝ) ≤ stT307 79 := by
  have hc : ((-197697/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6950828823/62500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-197697/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c80 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((421613/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 28377/200000) (δ := 7769/500000000) (ψ := 56493/500000) 307 214
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t80 : ((471321345579/5000000000000 : ℚ) : ℝ) ≤ stT307 80 := by
  have hc : ((421563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((471321345579/5000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((421563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c81 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-325123/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -950969/2000000) (δ := 7679/500000000) (ψ := 56493/500000) 307 215
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t81 : ((-45169897247/1250000000000 : ℚ) : ℝ) ≤ stT307 81 := by
  have hc : ((-325223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45169897247/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-325223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c82 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-289961/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4662457/10000000) (δ := 3089/200000000) (ψ := 56493/500000) 307 215
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t82 : ((-80079750819/2500000000000 : ℚ) : ℝ) ≤ stT307 82 := by
  have hc : ((-290061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80079750819/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-290061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c83 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((153363/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -435583/2500000) (δ := 1919/125000000) (ψ := 56493/500000) 307 216
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t83 : ((84157858603/1000000000000 : ℚ) : ℝ) ≤ stT307 83 := by
  have hc : ((153343/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84157858603/1000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((153343/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c84 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-986931/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7449363/10000000) (δ := 30751/1000000000) (ψ := 56493/500000) 307 216
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t84 : ((-107693965379/1000000000000 : ℚ) : ℝ) ≤ stT307 84 := by
  have hc : ((-987031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107693965379/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-987031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c85 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((59133/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 41217/500000) (δ := 3861/250000000) (ψ := 56493/500000) 307 217
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t85 : ((64131947641/625000000000 : ℚ) : ℝ) ≤ stT307 85 := by
  have hc : ((236507/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64131947641/625000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((236507/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c86 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-355873/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5906943/10000000) (δ := 15367/1000000000) (ψ := 56493/500000) 307 218
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t86 : ((-47975217093/625000000000 : ℚ) : ℝ) ≤ stT307 86 := by
  have hc : ((-355923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47975217093/625000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-355923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c87 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((187491/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 92689/312500) (δ := 15467/1000000000) (ψ := 56493/500000) 307 218
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t87 : ((12559859087/312500000000 : ℚ) : ℝ) ≤ stT307 87 := by
  have hc : ((187441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12559859087/312500000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((187441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c88 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-8679/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -992597/2500000) (δ := 7737/500000000) (ψ := 56493/500000) 307 219
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t88 : ((-2326287229/1250000000000 : ℚ) : ℝ) ≤ stT307 88 := by
  have hc : ((-8729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2326287229/1250000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-8729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c89 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-152527/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2350989/5000000) (δ := 7687/500000000) (ψ := 56493/500000) 307 219
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t89 : ((-80865657423/2500000000000 : ℚ) : ℝ) ≤ stT307 89 := by
  have hc : ((-152577/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80865657423/2500000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-152577/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c90 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((563491/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1215239/5000000) (δ := 7761/500000000) (ψ := 56493/500000) 307 220
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t90 : ((148466486493/2500000000000 : ℚ) : ℝ) ≤ stT307 90 := by
  have hc : ((563391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148466486493/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((563391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c91 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-750829/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3025141/5000000) (δ := 15411/500000000) (ψ := 56493/500000) 307 220
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t91 : ((-157437521353/2000000000000 : ℚ) : ℝ) ≤ stT307 91 := by
  have hc : ((-750929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157437521353/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-750929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c92 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((87379/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -253927/2000000) (δ := 3847/250000000) (ψ := 56493/500000) 307 221
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t92 : ((22772118267/250000000000 : ℚ) : ℝ) ≤ stT307 92 := by
  have hc : ((87369/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22772118267/250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((87369/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c93 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-23647/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7027731/10000000) (δ := 121/7812500) (ψ := 56493/500000) 307 221
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t93 : ((-6130849081/62500000000 : ℚ) : ℝ) ≤ stT307 93 := by
  have hc : ((-47299/50000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6130849081/62500000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-47299/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c94 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((982261/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47159/1000000) (δ := 963/62500000) (ψ := 56493/500000) 307 222
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t94 : ((1013021480781/10000000000000 : ℚ) : ℝ) ≤ stT307 94 := by
  have hc : ((982161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1013021480781/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((982161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c95 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-996679/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1912543/2500000) (δ := 3079/200000000) (ψ := 56493/500000) 307 222
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t95 : ((-1022674321641/10000000000000 : ℚ) : ℝ) ≤ stT307 95 := by
  have hc : ((-996779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1022674321641/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-996779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c96 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((249991/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21069/10000000) (δ := 31/2000000) (ψ := 56493/500000) 307 223
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t96 : ((6378007473/62500000000 : ℚ) : ℝ) ≤ stT307 96 := by
  have hc : ((124983/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6378007473/62500000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((124983/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c97 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-249877/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7775583/10000000) (δ := 15393/1000000000) (ψ := 56493/500000) 307 224
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t97 : ((-126868622997/1250000000000 : ℚ) : ℝ) ≤ stT307 97 := by
  have hc : ((-124951/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126868622997/1250000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-124951/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c98 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((499629/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 96281/10000000) (δ := 1541/100000000) (ψ := 56493/500000) 307 224
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t98 : ((63081340751/625000000000 : ℚ) : ℝ) ≤ stT307 98 := by
  have hc : ((499579/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63081340751/625000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((499579/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c99 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-499953/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1563943/2000000) (δ := 15517/1000000000) (ψ := 56493/500000) 307 225
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t99 : ((-251261007557/2500000000000 : ℚ) : ℝ) ≤ stT307 99 := by
  have hc : ((-500003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251261007557/2500000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-500003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c100 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((999099/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10611/1000000) (δ := 15417/1000000000) (ψ := 56493/500000) 307 225
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t100 : ((998998001001/10000000000000 : ℚ) : ℝ) ≤ stT307 100 := by
  have hc : ((998999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((998998001001/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((998999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c101 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-991657/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3765411/5000000) (δ := 15417/1000000000) (ψ := 56493/500000) 307 225
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t101 : ((-493417950883/5000000000000 : ℚ) : ℝ) ≤ stT307 101 := by
  have hc : ((-991757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-493417950883/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-991757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c102 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((193969/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -615501/10000000) (δ := 241/15625000) (ψ := 56493/500000) 307 226
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t102 : ((192038020503/2000000000000 : ℚ) : ℝ) ≤ stT307 102 := by
  have hc : ((193949/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192038020503/2000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((193949/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c103 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-923891/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3436153/5000000) (δ := 3881/250000000) (ψ := 56493/500000) 307 226
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t103 : ((-91043605203/1000000000000 : ℚ) : ℝ) ≤ stT307 103 := by
  have hc : ((-923991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91043605203/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-923991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c104 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((421473/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1420149/10000000) (δ := 15531/1000000000) (ψ := 56493/500000) 307 227
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t104 : ((20661948267/250000000000 : ℚ) : ℝ) ≤ stT307 104 := by
  have hc : ((421423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20661948267/250000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((421423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c105 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-143329/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2962221/5000000) (δ := 15431/1000000000) (ψ := 56493/500000) 307 227
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t105 : ((-139894432449/2000000000000 : ℚ) : ℝ) ≤ stT307 105 := by
  have hc : ((-143349/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139894432449/2000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-143349/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c106 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((268699/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2508619/10000000) (δ := 7719/500000000) (ψ := 56493/500000) 307 228
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t106 : ((52186948793/1000000000000 : ℚ) : ℝ) ≤ stT307 106 := by
  have hc : ((268649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52186948793/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((268649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c107 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-151779/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1174513/2500000) (δ := 3093/200000000) (ψ := 56493/500000) 307 228
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t107 : ((-146778711973/5000000000000 : ℚ) : ℝ) ≤ stT307 107 := by
  have hc : ((-151829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146778711973/5000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-151829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c108 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((22667/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3870319/10000000) (δ := 15357/1000000000) (ψ := 56493/500000) 307 229
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t108 : ((86860383/40000000000 : ℚ) : ℝ) ≤ stT307 108 := by
  have hc : ((22567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86860383/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((22567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c109 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((71351/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1601711/5000000) (δ := 7773/500000000) (ψ := 56493/500000) 307 229
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t109 : ((17079474319/625000000000 : ℚ) : ℝ) ≤ stT307 109 := by
  have hc : ((35663/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17079474319/625000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((35663/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c110 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-146749/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1373837/2500000) (δ := 15353/1000000000) (ψ := 56493/500000) 307 230
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t110 : ((-69971789181/1250000000000 : ℚ) : ℝ) ≤ stT307 110 := by
  have hc : ((-73387/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69971789181/1250000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-73387/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c111 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((209091/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29009/200000) (δ := 309/20000000) (ψ := 56493/500000) 307 230
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t111 : ((99218228681/1250000000000 : ℚ) : ℝ) ≤ stT307 111 := by
  have hc : ((104533/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99218228681/1250000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((104533/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c112 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-196327/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7374113/10000000) (δ := 15543/1000000000) (ψ := 56493/500000) 307 231
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t112 : ((-11595664779/125000000000 : ℚ) : ℝ) ≤ stT307 112 := by
  have hc : ((-196347/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11595664779/125000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-196347/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c113 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((48787/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -110361/2000000) (δ := 6/390625) (ψ := 56493/500000) 307 231
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t113 : ((286813769/3125000000 : ℚ) : ℝ) ≤ stT307 113 := by
  have hc : ((24391/25000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((286813769/3125000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((24391/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c114 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-791547/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 621033/1000000) (δ := 15543/1000000000) (ψ := 56493/500000) 307 231
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t114 : ((-370722748571/5000000000000 : ℚ) : ℝ) ≤ stT307 114 := by
  have hc : ((-791647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-370722748571/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-791647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c115 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((87531/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1397259/5000000) (δ := 15367/1000000000) (ψ := 56493/500000) 307 232
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t115 : ((10200544693/250000000000 : ℚ) : ℝ) ≤ stT307 115 := by
  have hc : ((87511/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10200544693/250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((87511/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c116 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((30593/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3850497/10000000) (δ := 15367/1000000000) (ψ := 56493/500000) 307 232
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t116 : ((7078004667/2500000000000 : ℚ) : ℝ) ≤ stT307 116 := by
  have hc : ((30493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7078004667/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((30493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c117 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-511529/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -26347/50000) (δ := 15429/1000000000) (ψ := 56493/500000) 307 233
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t117 : ((-473001522129/10000000000000 : ℚ) : ℝ) ≤ stT307 117 := by
  have hc : ((-511629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-473001522129/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-511629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c118 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((437581/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 631281/5000000) (δ := 15529/1000000000) (ψ := 56493/500000) 307 233
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t118 : ((201389831397/2500000000000 : ℚ) : ℝ) ≤ stT307 118 := by
  have hc : ((437531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201389831397/2500000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((437531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c119 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-998949/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7739341/10000000) (δ := 15529/1000000000) (ψ := 56493/500000) 307 233
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t119 : ((-915827219251/10000000000000 : ℚ) : ℝ) ≤ stT307 119 := by
  have hc : ((-999049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-915827219251/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-999049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c120 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((407409/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48311/312500) (δ := 15521/1000000000) (ψ := 56493/500000) 307 234
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t120 : ((37186581033/500000000000 : ℚ) : ℝ) ≤ stT307 120 := by
  have hc : ((407359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37186581033/500000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((407359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c121 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-350921/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4823377/10000000) (δ := 15521/1000000000) (ψ := 56493/500000) 307 234
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t121 : ((-319110031911/10000000000000 : ℚ) : ℝ) ≤ stT307 121 := by
  have hc : ((-351021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-319110031911/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-351021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c122 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-126739/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4567677/10000000) (δ := 15389/1000000000) (ψ := 56493/500000) 307 235
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t122 : ((-57394717731/2500000000000 : ℚ) : ℝ) ≤ stT307 122 := by
  have hc : ((-126789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57394717731/2500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-126789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c123 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((389081/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 212207/1250000) (δ := 15489/1000000000) (ψ := 56493/500000) 307 235
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t123 : ((350777192739/5000000000000 : ℚ) : ℝ) ≤ stT307 123 := by
  have hc : ((389031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((350777192739/5000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((389031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c124 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-62483/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7795707/10000000) (δ := 15507/1000000000) (ψ := 56493/500000) 307 236
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t124 : ((-224468134839/2500000000000 : ℚ) : ℝ) ≤ stT307 124 := by
  have hc : ((-249957/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224468134839/2500000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-249957/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c125 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((794631/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1630993/10000000) (δ := 3849/250000000) (ψ := 56493/500000) 307 236
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t125 : ((710649978737/10000000000000 : ℚ) : ℝ) ≤ stT307 125 := by
  have hc : ((794531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((710649978737/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((794531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c126 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-221199/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 22423/50000) (δ := 15507/1000000000) (ψ := 56493/500000) 307 236
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t126 : ((-197148861429/10000000000000 : ℚ) : ℝ) ≤ stT307 126 := by
  have hc : ((-221299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-197148861429/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-221299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c127 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-47211/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5156199/10000000) (δ := 31/2000000) (ψ := 56493/500000) 307 237
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t127 : ((-41901884897/1000000000000 : ℚ) : ℝ) ≤ stT307 127 := by
  have hc : ((-47221/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41901884897/1000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-47221/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c128 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((470473/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 863457/10000000) (δ := 31/2000000) (ψ := 56493/500000) 307 237
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t128 : ((415798892509/5000000000000 : ℚ) : ℝ) ≤ stT307 128 := by
  have hc : ((470423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((415798892509/5000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((470423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c129 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-918283/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 854537/1250000) (δ := 15403/1000000000) (ψ := 56493/500000) 307 237
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t129 : ((-808591230733/10000000000000 : ℚ) : ℝ) ≤ stT307 129 := by
  have hc : ((-918383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-808591230733/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-918383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c130 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((382761/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -368129/1250000) (δ := 1551/100000000) (ψ := 56493/500000) 307 238
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t130 : ((167807945669/5000000000000 : ℚ) : ℝ) ≤ stT307 130 := by
  have hc : ((382661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167807945669/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((382661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c131 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((386007/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2936243/10000000) (δ := 15493/1000000000) (ψ := 56493/500000) 307 238
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t131 : ((42146061191/1250000000000 : ℚ) : ℝ) ≤ stT307 131 := by
  have hc : ((385907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42146061191/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((385907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c132 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-466611/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6935189/10000000) (δ := 15517/1000000000) (ψ := 56493/500000) 307 239
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t132 : ((-406176601129/5000000000000 : ℚ) : ℝ) ≤ stT307 132 := by
  have hc : ((-466661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-406176601129/5000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-466661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c133 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((897343/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1142713/10000000) (δ := 15517/1000000000) (ψ := 56493/500000) 307 239
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t133 : ((778007480487/10000000000000 : ℚ) : ℝ) ≤ stT307 133 := by
  have hc : ((897243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((778007480487/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((897243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c134 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-53683/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 115159/250000) (δ := 15443/500000000) (ψ := 56493/500000) 307 239
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t134 : ((-46392356907/2000000000000 : ℚ) : ℝ) ≤ stT307 134 := by
  have hc : ((-53703/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46392356907/2000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-53703/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c135 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-34633/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5395279/10000000) (δ := 7739/500000000) (ψ := 56493/500000) 307 240
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t135 : ((-119250883291/2500000000000 : ℚ) : ℝ) ≤ stT307 135 := by
  have hc : ((-138557/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119250883291/2500000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-138557/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c136 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((994219/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 67237/2500000) (δ := 7689/500000000) (ψ := 56493/500000) 307 240
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t136 : ((213112272387/2500000000000 : ℚ) : ℝ) ≤ stT307 136 := by
  have hc : ((994119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213112272387/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((994119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c137 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-353729/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 589173/1000000) (δ := 617/40000000) (ψ := 56493/500000) 307 240
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t137 : ((-151126959441/2500000000000 : ℚ) : ℝ) ≤ stT307 137 := by
  have hc : ((-353779/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151126959441/2500000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-353779/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c138 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-30667/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1058609/2500000) (δ := 1929/125000000) (ψ := 56493/500000) 307 241
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t138 : ((-6531694961/625000000000 : ℚ) : ℝ) ≤ stT307 138 := by
  have hc : ((-7673/62500 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6531694961/625000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-7673/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c139 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((216599/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 163393/1250000) (δ := 15371/1000000000) (ψ := 56493/500000) 307 241
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t139 : ((22961933489/312500000000 : ℚ) : ℝ) ≤ stT307 139 := by
  have hc : ((108287/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22961933489/312500000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((108287/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c140 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-9139/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 851121/1250000) (δ := 1929/125000000) (ψ := 56493/500000) 307 241
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t140 : ((-77247167/1000000000 : ℚ) : ℝ) ≤ stT307 140 := by
  have hc : ((-457/500 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77247167/1000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-457/500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c141 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((194983/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3436391/10000000) (δ := 3841/250000000) (ψ := 56493/500000) 307 242
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t141 : ((164120913333/10000000000000 : ℚ) : ℝ) ≤ stT307 141 := by
  have hc : ((194883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164120913333/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((194883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c142 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((87529/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 397537/2000000) (δ := 3841/250000000) (ψ := 56493/500000) 307 242
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t142 : ((146884367973/2500000000000 : ℚ) : ℝ) ≤ stT307 142 := by
  have hc : ((175033/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146884367973/2500000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((175033/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c143 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-981603/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7373693/10000000) (δ := 3841/250000000) (ψ := 56493/500000) 307 242
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t143 : ((-820942261829/10000000000000 : ℚ) : ℝ) ≤ stT307 143 := by
  have hc : ((-981703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-820942261829/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-981703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c144 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((18381/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -298587/1000000) (δ := 15457/1000000000) (ψ := 56493/500000) 307 243
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t144 : ((1914165901/62500000000 : ℚ) : ℝ) ≤ stT307 144 := by
  have hc : ((2297/6250 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1914165901/62500000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((2297/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c145 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((597637/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1162807/5000000) (δ := 15357/1000000000) (ψ := 56493/500000) 307 243
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t145 : ((248113495899/5000000000000 : ℚ) : ℝ) ≤ stT307 145 := by
  have hc : ((597537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((248113495899/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((597537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c146 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-994867/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1520113/2000000) (δ := 7723/500000000) (ψ := 56493/500000) 307 243
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t146 : ((-411720329501/5000000000000 : ℚ) : ℝ) ≤ stT307 146 := by
  have hc : ((-994967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-411720329501/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-994967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c147 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((102713/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71713/250000) (δ := 15453/1000000000) (ψ := 56493/500000) 307 244
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t147 : ((1323369137/39062500000 : ℚ) : ℝ) ≤ stT307 147 := by
  have hc : ((6418/15625 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1323369137/39062500000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((6418/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c148 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((118931/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2334899/10000000) (δ := 311/20000000) (ψ := 56493/500000) 307 244
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t148 : ((48872064267/1000000000000 : ℚ) : ℝ) ≤ stT307 148 := by
  have hc : ((118911/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48872064267/1000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((118911/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c149 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-990179/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7503321/10000000) (δ := 309/20000000) (ψ := 56493/500000) 307 244
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t149 : ((-25352132679/312500000000 : ℚ) : ℝ) ≤ stT307 149 := by
  have hc : ((-990279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25352132679/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-990279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c150 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((335779/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3070911/10000000) (δ := 773/50000000) (ψ := 56493/500000) 307 245
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t150 : ((17130035049/625000000000 : ℚ) : ℝ) ≤ stT307 150 := by
  have hc : ((335679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17130035049/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((335679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c151 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((688391/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2028819/10000000) (δ := 15443/1000000000) (ψ := 56493/500000) 307 245
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t151 : ((140030739077/2500000000000 : ℚ) : ℝ) ≤ stT307 151 := by
  have hc : ((688291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140030739077/2500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((688291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c152 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-954251/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 886857/1250000) (δ := 15543/1000000000) (ψ := 56493/500000) 307 245
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t152 : ((-193520432727/2500000000000 : ℚ) : ℝ) ≤ stT307 152 := by
  have hc : ((-954351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193520432727/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-954351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c153 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((138231/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1790151/5000000) (δ := 3867/250000000) (ψ := 56493/500000) 307 246
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t153 : ((27918070803/2500000000000 : ℚ) : ℝ) ≤ stT307 153 := by
  have hc : ((138131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27918070803/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((138131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c154 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((843037/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 141973/1000000) (δ := 1921/125000000) (ψ := 56493/500000) 307 246
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t154 : ((339628589607/5000000000000 : ℚ) : ℝ) ≤ stT307 154 := by
  have hc : ((842937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((339628589607/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((842937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c155 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-208201/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3193687/5000000) (δ := 3867/250000000) (ψ := 56493/500000) 307 246
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t155 : ((-4181282193/62500000000 : ℚ) : ℝ) ≤ stT307 155 := by
  have hc : ((-104113/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4181282193/62500000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-104113/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c156 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-182131/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2192437/5000000) (δ := 3857/250000000) (ψ := 56493/500000) 307 247
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t156 : ((-145901610071/10000000000000 : ℚ) : ℝ) ≤ stT307 156 := by
  have hc : ((-182231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145901610071/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-182231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c157 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((122313/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 259649/5000000) (δ := 619/40000000) (ψ := 56493/500000) 307 247
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t157 : ((97606316843/1250000000000 : ℚ) : ℝ) ≤ stT307 157 := by
  have hc : ((244601/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97606316843/1250000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((244601/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c158 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-553139/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5392309/10000000) (δ := 619/40000000) (ψ := 56493/500000) 307 247
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t158 : ((-220066856181/5000000000000 : ℚ) : ℝ) ≤ stT307 158 := by
  have hc : ((-553239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220066856181/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-553239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c159 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-579847/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -85521/156250) (δ := 15521/1000000000) (ψ := 56493/500000) 307 248
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t159 : ((-114982032061/2500000000000 : ℚ) : ℝ) ≤ stT307 159 := by
  have hc : ((-579947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114982032061/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-579947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c160 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((193041/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -330713/5000000) (δ := 15521/1000000000) (ψ := 56493/500000) 307 248
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t160 : ((152596418949/2000000000000 : ℚ) : ℝ) ≤ stT307 160 := by
  have hc : ((193021/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152596418949/2000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((193021/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c161 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-1933/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4120483/10000000) (δ := 15421/1000000000) (ψ := 56493/500000) 307 248
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t161 : ((-3050777681/500000000000 : ℚ) : ℝ) ≤ stT307 161 := by
  have hc : ((-3871/50000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3050777681/500000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-3871/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c162 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-918097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -85439/125000) (δ := 15389/1000000000) (ψ := 56493/500000) 307 249
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t162 : ((-28856177119/400000000000 : ℚ) : ℝ) ≤ stT307 162 := by
  have hc : ((-918197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28856177119/400000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-918197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c163 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((16597/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1056001/5000000) (δ := 7707/500000000) (ψ := 56493/500000) 307 249
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t163 : ((1299780807/25000000000 : ℚ) : ℝ) ≤ stT307 163 := by
  have hc : ((33189/50000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1299780807/25000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((33189/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c164 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((256177/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1291091/5000000) (δ := 15489/1000000000) (ψ := 56493/500000) 307 249
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t164 : ((50000344559/1250000000000 : ℚ) : ℝ) ≤ stT307 164 := by
  have hc : ((256127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50000344559/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((256127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c165 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-970749/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3623907/5000000) (δ := 7707/500000000) (ψ := 56493/500000) 307 249
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t165 : ((-755804975651/10000000000000 : ℚ) : ℝ) ≤ stT307 165 := by
  have hc : ((-970849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-755804975651/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-970849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c166 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((41711/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -955671/2500000) (δ := 15407/1000000000) (ψ := 56493/500000) 307 250
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t166 : ((645927553/200000000000 : ℚ) : ℝ) ≤ stT307 166 := by
  have hc : ((41611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((645927553/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((41611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c167 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((950859/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 393499/5000000) (δ := 3849/250000000) (ψ := 56493/500000) 307 250
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t167 : ((735719181657/10000000000000 : ℚ) : ℝ) ≤ stT307 167 := by
  have hc : ((950759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((735719181657/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((950759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c168 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-136341/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 107381/200000) (δ := 1937/125000000) (ψ := 56493/500000) 307 250
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t168 : ((-52604343611/1250000000000 : ℚ) : ℝ) ≤ stT307 168 := by
  have hc : ((-68183/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52604343611/1250000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-68183/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c169 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-338171/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1156791/2000000) (δ := 15499/1000000000) (ψ := 56493/500000) 307 251
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t169 : ((-260170078051/5000000000000 : ℚ) : ℝ) ≤ stT307 169 := by
  have hc : ((-338221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-260170078051/5000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-338221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c170 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((438221/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -251187/2000000) (δ := 15399/1000000000) (ψ := 56493/500000) 307 251
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t170 : ((84015345711/1250000000000 : ℚ) : ℝ) ≤ stT307 170 := by
  have hc : ((438171/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84015345711/1250000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((438171/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c171 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((134611/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3245529/10000000) (δ := 15499/1000000000) (ψ := 56493/500000) 307 251
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t171 : ((102901353359/5000000000000 : ℚ) : ℝ) ≤ stT307 171 := by
  have hc : ((134561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102901353359/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((134561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c172 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-49929/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1544149/2000000) (δ := 15399/1000000000) (ψ := 56493/500000) 307 251
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t172 : ((-19037162731/250000000000 : ℚ) : ℝ) ≤ stT307 172 := by
  have hc : ((-24967/25000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19037162731/250000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-24967/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c173 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((154991/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -442243/1250000) (δ := 481/31250000) (ψ := 56493/500000) 307 252
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t173 : ((23552260787/2000000000000 : ℚ) : ℝ) ≤ stT307 173 := by
  have hc : ((154891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23552260787/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((154891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c174 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((937897/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13839/156250) (δ := 15411/1000000000) (ψ := 56493/500000) 307 252
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t174 : ((355471015053/5000000000000 : ℚ) : ℝ) ≤ stT307 174 := by
  have hc : ((937797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((355471015053/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((937797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c175 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-516541/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 660501/1250000) (δ := 481/31250000) (ψ := 56493/500000) 307 252
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t175 : ((-390543914489/10000000000000 : ℚ) : ℝ) ≤ stT307 175 := by
  have hc : ((-516641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-390543914489/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-516641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c176 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-15019/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -302537/500000) (δ := 7709/500000000) (ψ := 56493/500000) 307 253
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t176 : ((-11322514359/200000000000 : ℚ) : ℝ) ≤ stT307 176 := by
  have hc : ((-15021/20000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11322514359/200000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-15021/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c177 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((777009/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1702239/10000000) (δ := 3097/200000000) (ψ := 56493/500000) 307 253
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t177 : ((291980271107/5000000000000 : ℚ) : ℝ) ≤ stT307 177 := by
  have hc : ((776909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((291980271107/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((776909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c178 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((99743/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2621703/10000000) (δ := 7709/500000000) (ψ := 56493/500000) 307 253
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t178 : ((74745479913/2000000000000 : ℚ) : ℝ) ≤ stT307 178 := by
  have hc : ((99723/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74745479913/2000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((99723/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c179 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-232809/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1730367/2500000) (δ := 3077/200000000) (ψ := 56493/500000) 307 253
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t179 : ((-21753564203/312500000000 : ℚ) : ℝ) ≤ stT307 179 := by
  have hc : ((-116417/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21753564203/312500000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-116417/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c180 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-231389/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4510753/10000000) (δ := 7739/500000000) (ψ := 56493/500000) 307 254
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t180 : ((-43135428771/2500000000000 : ℚ) : ℝ) ≤ stT307 180 := by
  have hc : ((-231489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43135428771/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-231489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c181 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((994653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -258649/10000000) (δ := 617/40000000) (ψ := 56493/500000) 307 254
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t181 : ((369622638791/5000000000000 : ℚ) : ℝ) ≤ stT307 181 := by
  have hc : ((994553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((369622638791/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((994553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c182 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-1719/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3969969/10000000) (δ := 617/40000000) (ψ := 56493/500000) 307 254
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t182 : ((-1025297/800000000 : ℚ) : ℝ) ≤ stT307 182 := by
  have hc : ((-1729/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1025297/800000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-1729/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c183 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-495871/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3766239/5000000) (δ := 1929/125000000) (ψ := 56493/500000) 307 255
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t183 : ((-183297856731/2500000000000 : ℚ) : ℝ) ≤ stT307 183 := by
  have hc : ((-495921/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183297856731/2500000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-495921/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c184 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((57197/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -334991/1000000) (δ := 1929/125000000) (ψ := 56493/500000) 307 255
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t184 : ((10536928237/625000000000 : ℚ) : ℝ) ≤ stT307 184 := by
  have hc : ((14293/62500 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10536928237/625000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((14293/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c185 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((947967/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 810017/10000000) (δ := 3883/250000000) (ψ := 56493/500000) 307 255
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t185 : ((348442544269/5000000000000 : ℚ) : ℝ) ≤ stT307 185 := by
  have hc : ((947867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348442544269/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((947867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c186 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-79389/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38652/78125) (δ := 3883/250000000) (ψ := 56493/500000) 307 255
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t186 : ((-14556384381/500000000000 : ℚ) : ℝ) ≤ stT307 186 := by
  have hc : ((-79409/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14556384381/500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-79409/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c187 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-442681/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6645173/10000000) (δ := 1933/125000000) (ψ := 56493/500000) 307 256
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t187 : ((-323757226563/5000000000000 : ℚ) : ℝ) ≤ stT307 187 := by
  have hc : ((-442731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-323757226563/5000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-442731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c188 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((52273/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -510373/2000000) (δ := 3841/250000000) (ψ := 56493/500000) 307 256
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t188 : ((9529165053/250000000000 : ℚ) : ℝ) ≤ stT307 188 := by
  have hc : ((52263/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9529165053/250000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((52263/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c189 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((410419/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1519799/10000000) (δ := 1933/125000000) (ψ := 56493/500000) 307 256
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t189 : ((9328097739/156250000000 : ℚ) : ℝ) ≤ stT307 189 := by
  have hc : ((410369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9328097739/156250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((410369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c190 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-610873/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5569897/10000000) (δ := 15439/1000000000) (ψ := 56493/500000) 307 256
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t190 : ((-443246859121/10000000000000 : ℚ) : ℝ) ≤ stT307 190 := by
  have hc : ((-610973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-443246859121/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-610973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c191 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-766173/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -190911/312500) (δ := 3839/250000000) (ψ := 56493/500000) 307 257
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t191 : ((-22178239439/400000000000 : ℚ) : ℝ) ≤ stT307 191 := by
  have hc : ((-766273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22178239439/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-766273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c192 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((333531/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65667/312500) (δ := 483/31250000) (ψ := 56493/500000) 307 257
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t192 : ((240668902447/5000000000000 : ℚ) : ℝ) ≤ stT307 192 := by
  have hc : ((333481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((240668902447/5000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((333481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c193 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((364387/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 377133/2000000) (δ := 483/31250000) (ψ := 56493/500000) 307 257
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t193 : ((52451047531/1000000000000 : ℚ) : ℝ) ≤ stT307 193 := by
  have hc : ((364337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52451047531/1000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((364337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c194 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-87021/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1170421/2000000) (δ := 483/31250000) (ψ := 56493/500000) 307 257
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t194 : ((-124972969253/2500000000000 : ℚ) : ℝ) ≤ stT307 194 := by
  have hc : ((-174067/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124972969253/2500000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-174067/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c195 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-356279/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2954917/5000000) (δ := 15549/1000000000) (ψ := 56493/500000) 307 258
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t195 : ((-51034508367/1000000000000 : ℚ) : ℝ) ≤ stT307 195 := by
  have hc : ((-356329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51034508367/1000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-356329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c196 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((140257/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -991997/5000000) (δ := 7727/500000000) (ψ := 56493/500000) 307 258
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t196 : ((20033837109/400000000000 : ℚ) : ℝ) ≤ stT307 196 := by
  have hc : ((140237/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20033837109/400000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((140237/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c197 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((89847/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 192189/1000000) (δ := 7677/500000000) (ψ := 56493/500000) 307 258
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t197 : ((12800877243/250000000000 : ℚ) : ℝ) ≤ stT307 197 := by
  have hc : ((179669/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12800877243/250000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((179669/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c198 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-170847/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5807973/10000000) (δ := 7727/500000000) (ψ := 56493/500000) 307 258
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t198 : ((-1517920053/31250000000 : ℚ) : ℝ) ≤ stT307 198 := by
  have hc : ((-21359/31250 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1517920053/31250000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-21359/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c199 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-746373/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6033479/10000000) (δ := 15361/1000000000) (ψ := 56493/500000) 307 259
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t199 : ((-264580636593/5000000000000 : ℚ) : ℝ) ≤ stT307 199 := by
  have hc : ((-746473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264580636593/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-746473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c200 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((641339/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -437277/2000000) (δ := 15461/1000000000) (ψ := 56493/500000) 307 259
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t200 : ((226711972167/5000000000000 : ℚ) : ℝ) ≤ stT307 200 := by
  have hc : ((641239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226711972167/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((641239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c201 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((49503/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 820799/5000000) (δ := 15461/1000000000) (ψ := 56493/500000) 307 259
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t201 : ((27929828103/500000000000 : ℚ) : ℝ) ≤ stT307 201 := by
  have hc : ((197987/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27929828103/500000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((197987/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c202 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-572369/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 545047/1000000) (δ := 15361/1000000000) (ψ := 56493/500000) 307 259
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t202 : ((-201394021731/5000000000000 : ℚ) : ℝ) ≤ stT307 202 := by
  have hc : ((-572469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-201394021731/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-572469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c203 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-850083/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1616837/2500000) (δ := 1921/125000000) (ψ := 56493/500000) 307 260
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t203 : ((-596711990929/10000000000000 : ℚ) : ℝ) ≤ stT307 203 := by
  have hc : ((-850183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-596711990929/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-850183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c204 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((472791/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2695853/10000000) (δ := 1921/125000000) (ψ := 56493/500000) 307 260
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t204 : ((16547493837/500000000000 : ℚ) : ℝ) ≤ stT307 204 := by
  have hc : ((472691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16547493837/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((472691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c205 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((911907/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 528611/5000000) (δ := 1921/125000000) (ψ := 56493/500000) 307 260
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t205 : ((63683336301/1000000000000 : ℚ) : ℝ) ≤ stT307 205 := by
  have hc : ((911807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63683336301/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((911807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c206 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-21197/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 479203/1000000) (δ := 3107/200000000) (ψ := 56493/500000) 307 260
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t206 : ((-29546050371/1250000000000 : ℚ) : ℝ) ≤ stT307 206 := by
  have hc : ((-84813/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29546050371/1250000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-84813/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c207 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-9659/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7199237/10000000) (δ := 619/40000000) (ψ := 56493/500000) 307 261
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t207 : ((-335708667/5000000000 : ℚ) : ℝ) ≤ stT307 207 := by
  have hc : ((-483/500 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-335708667/5000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-483/500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c208 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((849/5000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -140017/400000) (δ := 1941/125000000) (ψ := 56493/500000) 307 261
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t208 : ((9413259/800000000 : ℚ) : ℝ) ≤ stT307 208 := by
  have hc : ((1697/10000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9413259/800000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((1697/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c209 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((99739/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 180659/10000000) (δ := 123/8000000) (ψ := 56493/500000) 307 261
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t209 : ((34491972753/500000000000 : ℚ) : ℝ) ≤ stT307 209 := by
  have hc : ((99729/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34491972753/500000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((99729/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c210 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((33123/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3844167/10000000) (δ := 619/40000000) (ψ := 56493/500000) 307 261
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t210 : ((4557603299/2000000000000 : ℚ) : ℝ) ≤ stT307 210 := by
  have hc : ((33023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4557603299/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((33023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c211 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-197887/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1872563/2500000) (δ := 3857/250000000) (ψ := 56493/500000) 307 261
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t211 : ((-136244918103/2000000000000 : ℚ) : ℝ) ≤ stT307 211 := by
  have hc : ((-197907/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136244918103/2000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-197907/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c212 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-261679/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2294447/5000000) (δ := 15483/1000000000) (ψ := 56493/500000) 307 262
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t212 : ((-179790602537/10000000000000 : ℚ) : ℝ) ≤ stT307 212 := by
  have hc : ((-261779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179790602537/10000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-261779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c213 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((924587/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -244279/2500000) (δ := 15383/1000000000) (ψ := 56493/500000) 307 262
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t213 : ((158361849639/2500000000000 : ℚ) : ℝ) ≤ stT307 213 := by
  have hc : ((924487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158361849639/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((924487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c214 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((20003/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2617777/10000000) (δ := 771/50000000) (ψ := 56493/500000) 307 262
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t214 : ((2734203283/80000000000 : ℚ) : ℝ) ≤ stT307 214 := by
  have hc : ((19999/40000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2734203283/80000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((19999/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c215 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-787997/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3097931/5000000) (δ := 771/50000000) (ψ := 56493/500000) 307 262
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t215 : ((-107495642703/2000000000000 : ℚ) : ℝ) ≤ stT307 215 := by
  have hc : ((-788097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107495642703/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-788097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c216 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-361951/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2975297/5000000) (δ := 1539/100000000) (ψ := 56493/500000) 307 263
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t216 : ((-123155274207/2500000000000 : ℚ) : ℝ) ≤ stT307 216 := by
  have hc : ((-362001/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123155274207/2500000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-362001/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c217 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((571687/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -601397/2500000) (δ := 1549/100000000) (ψ := 56493/500000) 307 263
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t217 : ((97004601357/2500000000000 : ℚ) : ℝ) ≤ stT307 217 := by
  have hc : ((571587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97004601357/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((571587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c218 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((900769/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 561573/5000000) (δ := 15513/1000000000) (ψ := 56493/500000) 307 263
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t218 : ((122001920733/2000000000000 : ℚ) : ℝ) ≤ stT307 218 := by
  have hc : ((900669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122001920733/2000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((900669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c219 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-279727/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1158941/2500000) (δ := 1549/100000000) (ψ := 56493/500000) 307 263
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t219 : ((-94544868663/5000000000000 : ℚ) : ℝ) ≤ stT307 219 := by
  have hc : ((-279827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94544868663/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-279827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c220 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-62113/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7575623/10000000) (δ := 15397/1000000000) (ψ := 56493/500000) 307 264
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t220 : ((-837615967/12500000000 : ℚ) : ℝ) ≤ stT307 220 := by
  have hc : ((-248477/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-837615967/12500000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-248477/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c221 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-8387/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4094857/10000000) (δ := 15397/1000000000) (ψ := 56493/500000) 307 264
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t221 : ((-11300233727/2500000000000 : ℚ) : ℝ) ≤ stT307 221 := by
  have hc : ((-16799/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11300233727/2500000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-16799/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c222 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((38737/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -314951/5000000) (δ := 7753/500000000) (ψ := 56493/500000) 307 264
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t222 : ((6498971337/100000000000 : ℚ) : ℝ) ≤ stT307 222 := by
  have hc : ((38733/40000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6498971337/100000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((38733/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c223 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((42863/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56391/200000) (δ := 7753/500000000) (ψ := 56493/500000) 307 264
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t223 : ((28696468597/1000000000000 : ℚ) : ℝ) ≤ stT307 223 := by
  have hc : ((42853/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28696468597/1000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((42853/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c224 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-801999/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 781697/1250000) (δ := 15497/1000000000) (ψ := 56493/500000) 307 264
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t224 : ((-267962827623/5000000000000 : ℚ) : ℝ) ≤ stT307 224 := by
  have hc : ((-802099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-267962827623/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-802099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c225 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-746947/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1508909/2500000) (δ := 15499/1000000000) (ψ := 56493/500000) 307 265
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t225 : ((-498031582349/10000000000000 : ℚ) : ℝ) ≤ stT307 225 := by
  have hc : ((-747047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-498031582349/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-747047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c226 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((495099/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2632119/10000000) (δ := 30899/1000000000) (ψ := 56493/500000) 307 265
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t226 : ((32926838481/1000000000000 : ℚ) : ℝ) ≤ stT307 226 := by
  have hc : ((494999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32926838481/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((494999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c227 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((954573/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47277/625000) (δ := 15499/1000000000) (ψ := 56493/500000) 307 265
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t227 : ((633505682979/10000000000000 : ℚ) : ℝ) ≤ stT307 227 := by
  have hc : ((954473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((633505682979/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((954473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c228 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-5071/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 826011/2000000) (δ := 15499/1000000000) (ψ := 56493/500000) 307 265
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t228 : ((-13449980503/2500000000000 : ℚ) : ℝ) ≤ stT307 228 := by
  have hc : ((-20309/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13449980503/2500000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-20309/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c229 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-989359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3744471/5000000) (δ := 15499/1000000000) (ψ := 56493/500000) 307 265
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t229 : ((-653853306921/10000000000000 : ℚ) : ℝ) ≤ stT307 229 := by
  have hc : ((-989459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-653853306921/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-989459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c230 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-46263/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4874793/10000000) (δ := 15411/1000000000) (ψ := 56493/500000) 307 266
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t230 : ((-61026370931/2500000000000 : ℚ) : ℝ) ≤ stT307 230 := by
  have hc : ((-92551/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61026370931/2500000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-92551/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c231 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((407511/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1545071/10000000) (δ := 15411/1000000000) (ψ := 56493/500000) 307 266
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t231 : ((268089372411/5000000000000 : ℚ) : ℝ) ≤ stT307 231 := by
  have hc : ((407461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268089372411/5000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((407461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c232 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((379803/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 885111/5000000) (δ := 15411/1000000000) (ψ := 56493/500000) 307 266
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t232 : ((62329999149/1250000000000 : ℚ) : ℝ) ≤ stT307 232 := by
  have hc : ((379753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62329999149/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((379753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c233 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-441913/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1267829/2500000) (δ := 481/31250000) (ψ := 56493/500000) 307 266
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t233 : ((-144786220293/5000000000000 : ℚ) : ℝ) ≤ stT307 233 := by
  have hc : ((-442013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144786220293/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-442013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c234 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-979723/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -293987/400000) (δ := 3077/200000000) (ψ := 56493/500000) 307 267
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t234 : ((-640530871383/10000000000000 : ℚ) : ℝ) ≤ stT307 234 := by
  have hc : ((-979823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-640530871383/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-979823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c235 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-59867/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1019187/2500000) (δ := 3077/200000000) (ψ := 56493/500000) 307 267
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t235 : ((-39118213143/10000000000000 : ℚ) : ℝ) ≤ stT307 235 := by
  have hc : ((-59967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39118213143/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-59967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c236 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((946983/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -817713/10000000) (δ := 3097/200000000) (ψ := 56493/500000) 307 267
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t236 : ((9630746993/156250000000 : ℚ) : ℝ) ≤ stT307 236 := by
  have hc : ((946883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9630746993/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((946883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c237 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((70559/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 606877/2500000) (δ := 7759/500000000) (ψ := 56493/500000) 307 267
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t237 : ((91649638917/2500000000000 : ℚ) : ℝ) ≤ stT307 237 := by
  have hc : ((141093/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91649638917/2500000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((141093/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c238 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-638717/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2829533/5000000) (δ := 3097/200000000) (ψ := 56493/500000) 307 267
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t238 : ((-103520933667/2500000000000 : ℚ) : ℝ) ≤ stT307 238 := by
  have hc : ((-638817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103520933667/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-638817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c239 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-458709/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3415423/5000000) (δ := 7713/500000000) (ψ := 56493/500000) 307 268
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t239 : ((-296746882873/5000000000000 : ℚ) : ℝ) ≤ stT307 239 := by
  have hc : ((-458759/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-296746882873/5000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-458759/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c240 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((7501/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3626227/10000000) (δ := 15477/1000000000) (ψ := 56493/500000) 307 268
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t240 : ((19351354563/2500000000000 : ℚ) : ℝ) ≤ stT307 240 := by
  have hc : ((29979/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19351354563/2500000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((29979/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c241 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((984903/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -217481/5000000) (δ := 15477/1000000000) (ψ := 56493/500000) 307 268
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t241 : ((158591690317/2500000000000 : ℚ) : ℝ) ≤ stT307 241 := by
  have hc : ((984803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158591690317/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((984803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c242 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((456053/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1371551/5000000) (δ := 15477/1000000000) (ψ := 56493/500000) 307 268
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t242 : ((36637191409/1250000000000 : ℚ) : ℝ) ≤ stT307 242 := by
  have hc : ((455953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36637191409/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((455953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c243 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-142411/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2954021/5000000) (δ := 15377/1000000000) (ψ := 56493/500000) 307 268
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t243 : ((-91369628931/2000000000000 : ℚ) : ℝ) ≤ stT307 243 := by
  have hc : ((-142431/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91369628931/2000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-142431/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c244 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-885879/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -415497/625000) (δ := 15433/1000000000) (ψ := 56493/500000) 307 269
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t244 : ((-113438093223/2000000000000 : ℚ) : ℝ) ≤ stT307 244 := by
  have hc : ((-885979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113438093223/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-885979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c245 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((41613/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -877229/2500000) (δ := 3087/100000000) (ψ := 56493/500000) 307 269
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t245 : ((1660598443/156250000000 : ℚ) : ℝ) ≤ stT307 245 := by
  have hc : ((10397/62500 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1660598443/156250000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((10397/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c246 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((988311/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -382619/10000000) (δ := 15533/1000000000) (ψ := 56493/500000) 307 269
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t246 : ((78757452067/1250000000000 : ℚ) : ℝ) ≤ stT307 246 := by
  have hc : ((988211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78757452067/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((988211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c247 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((92073/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109239/400000) (δ := 15533/1000000000) (ψ := 56493/500000) 307 269
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t247 : ((14642962763/500000000000 : ℚ) : ℝ) ≤ stT307 247 := by
  have hc : ((92053/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14642962763/500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((92053/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c248 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-690367/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2915991/5000000) (δ := 15533/1000000000) (ψ := 56493/500000) 307 269
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t248 : ((-438447235467/10000000000000 : ℚ) : ℝ) ≤ stT307 248 := by
  have hc : ((-690467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-438447235467/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-690467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c249 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-455189/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1357497/2000000) (δ := 15363/1000000000) (ψ := 56493/500000) 307 270
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t249 : ((-11539853411/200000000000 : ℚ) : ℝ) ≤ stT307 249 := by
  have hc : ((-455239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11539853411/200000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-455239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c250 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((43091/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -927817/2500000) (δ := 193/12500000) (ψ := 56493/500000) 307 270
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t250 : ((5444299131/1000000000000 : ℚ) : ℝ) ≤ stT307 250 := by
  have hc : ((43041/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5444299131/1000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((43041/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c251 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((15104/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40463/625000) (δ := 193/12500000) (ψ := 56493/500000) 307 270
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t251 : ((76260543483/1250000000000 : ℚ) : ℝ) ≤ stT307 251 := by
  have hc : ((241639/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76260543483/1250000000000 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((241639/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c252 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((572127/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2404249/10000000) (δ := 777/50000000) (ψ := 56493/500000) 307 270
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t252 : ((18017134419/500000000000 : ℚ) : ℝ) ≤ stT307 252 := by
  have hc : ((572027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).1
  have hw2 : ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31497/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18017134419/500000000000 : ℚ) : ℝ)
      = ((31497/500000 : ℚ) : ℝ) * ((572027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c253 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-570197/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 340241/625000) (δ := 777/50000000) (ψ := 56493/500000) 307 270
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t253 : ((-71708574483/2000000000000 : ℚ) : ℝ) ≤ stT307 253 := by
  have hc : ((-570297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71708574483/2000000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-570297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c254 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-19393/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3618237/5000000) (δ := 483/31250000) (ψ := 56493/500000) 307 271
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t254 : ((-9507429/156250000 : ℚ) : ℝ) ≤ stT307 254 := by
  have hc : ((-3879/4000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9507429/156250000 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-3879/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c255 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-29307/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65949/156250) (δ := 3839/250000000) (ψ := 56493/500000) 307 271
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t255 : ((-183684317/25000000000 : ℚ) : ℝ) ≤ stT307 255 := by
  have hc : ((-7333/62500 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183684317/25000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-7333/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c256 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((220967/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -608409/5000000) (δ := 483/31250000) (ψ := 56493/500000) 307 271
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t256 : ((110471/2000000 : ℚ) : ℝ) ≤ stT307 256 := by
  have hc : ((110471/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).1
  have hw2 : ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110471/2000000 : ℚ) : ℝ)
      = ((1/16 : ℚ) : ℝ) * ((110471/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c257 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((758269/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 887679/5000000) (δ := 15447/1000000000) (ψ := 56493/500000) 307 271
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t257 : ((236466087579/5000000000000 : ℚ) : ℝ) ≤ stT307 257 := by
  have hc : ((758169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((236466087579/5000000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((758169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c258 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-325539/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 594493/1250000) (δ := 3839/250000000) (ψ := 56493/500000) 307 271
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t258 : ((-202734049147/10000000000000 : ℚ) : ℝ) ≤ stT307 258 := by
  have hc : ((-325639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).2
  have h0 : (0:ℝ) ≤ ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202734049147/10000000000000 : ℚ) : ℝ)
      = ((622573/10000000 : ℚ) : ℝ) * ((-325639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c259 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-99867/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3862509/5000000) (δ := 15447/1000000000) (ψ := 56493/500000) 307 271
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t259 : ((-6206057149/100000000000 : ℚ) : ℝ) ≤ stT307 259 := by
  have hc : ((-99877/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).2
  have h0 : (0:ℝ) ≤ ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6206057149/100000000000 : ℚ) : ℝ)
      = ((62137/1000000 : ℚ) : ℝ) * ((-99877/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c260 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-42533/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1256327/2500000) (δ := 15549/1000000000) (ψ := 56493/500000) 307 272
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t260 : ((-13192031241/500000000000 : ℚ) : ℝ) ≤ stT307 260 := by
  have hc : ((-42543/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13192031241/500000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-42543/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c261 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((336843/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2079029/10000000) (δ := 15549/1000000000) (ψ := 56493/500000) 307 272
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t261 : ((26058684789/625000000000 : ℚ) : ℝ) ≤ stT307 261 := by
  have hc : ((336793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).1
  have hw2 : ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((77373/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26058684789/625000000000 : ℚ) : ℝ)
      = ((77373/1250000 : ℚ) : ℝ) * ((336793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c262 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((235489/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26749/312500) (δ := 46149/1000000000) (ψ := 56493/500000) 307 272
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t262 : ((9091883133/156250000000 : ℚ) : ℝ) ≤ stT307 262 := by
  have hc : ((29433/31250 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).1
  have hw2 : ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9091883133/156250000000 : ℚ) : ℝ)
      = ((308901/5000000 : ℚ) : ℝ) * ((29433/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c263 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((58859/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3779759/10000000) (δ := 15549/1000000000) (ψ := 56493/500000) 307 272
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t263 : ((18116163567/5000000000000 : ℚ) : ℝ) ≤ stT307 263 := by
  have hc : ((58759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18116163567/5000000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((58759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c264 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-223501/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6692499/10000000) (δ := 23077/500000000) (ψ := 56493/500000) 307 272
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t264 : ((-34392716227/625000000000 : ℚ) : ℝ) ≤ stT307 264 := by
  have hc : ((-111763/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).2
  have h0 : (0:ℝ) ≤ ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34392716227/625000000000 : ℚ) : ℝ)
      = ((307729/5000000 : ℚ) : ℝ) * ((-111763/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c265 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-2398/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6113777/10000000) (δ := 7731/500000000) (ψ := 56493/500000) 307 273
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t265 : ((-2946547551/62500000000 : ℚ) : ℝ) ≤ stT307 265 := by
  have hc : ((-38373/50000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).2
  have h0 : (0:ℝ) ≤ ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2946547551/62500000000 : ℚ) : ℝ)
      = ((76787/1250000 : ℚ) : ℝ) * ((-38373/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c266 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((138947/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3222989/10000000) (δ := 15541/1000000000) (ψ := 56493/500000) 307 273
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t266 : ((85163167683/5000000000000 : ℚ) : ℝ) ≤ stT307 266 := by
  have hc : ((138897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).1
  have hw2 : ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((613139/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85163167683/5000000000000 : ℚ) : ℝ)
      = ((613139/10000000 : ℚ) : ℝ) * ((138897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c267 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((990597/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -171549/5000000) (δ := 7731/500000000) (ψ := 56493/500000) 307 273
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t267 : ((60617425903/1000000000000 : ℚ) : ℝ) ≤ stT307 267 := by
  have hc : ((990497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).1
  have hw2 : ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61199/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60617425903/1000000000000 : ℚ) : ℝ)
      = ((61199/1000000 : ℚ) : ℝ) * ((990497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c268 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((265753/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2526047/10000000) (δ := 7681/500000000) (ψ := 56493/500000) 307 273
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t268 : ((162303880441/5000000000000 : ℚ) : ℝ) ≤ stT307 268 := by
  have hc : ((265703/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).1
  have hw2 : ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162303880441/5000000000000 : ℚ) : ℝ)
      = ((610847/10000000 : ℚ) : ℝ) * ((265703/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c269 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-275271/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1346131/2500000) (δ := 7681/500000000) (ψ := 56493/500000) 307 273
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t269 : ((-167866242231/5000000000000 : ℚ) : ℝ) ≤ stT307 269 := by
  have hc : ((-275321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).2
  have h0 : (0:ℝ) ≤ ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167866242231/5000000000000 : ℚ) : ℝ)
      = ((609711/10000000 : ℚ) : ℝ) * ((-275321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c270 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-197713/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3737777/5000000) (δ := 7717/500000000) (ψ := 56493/500000) 307 274
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t270 : ((-120336546873/2000000000000 : ℚ) : ℝ) ≤ stT307 270 := by
  have hc : ((-197733/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).2
  have h0 : (0:ℝ) ≤ ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120336546873/2000000000000 : ℚ) : ℝ)
      = ((608581/10000000 : ℚ) : ℝ) * ((-197733/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c271 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-56131/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4638183/10000000) (δ := 15369/1000000000) (ψ := 56493/500000) 307 274
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t271 : ((-34109318007/2000000000000 : ℚ) : ℝ) ≤ stT307 271 := by
  have hc : ((-56151/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).2
  have h0 : (0:ℝ) ≤ ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34109318007/2000000000000 : ℚ) : ℝ)
      = ((607457/10000000 : ℚ) : ℝ) * ((-56151/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c272 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((74881/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1811327/10000000) (δ := 15369/1000000000) (ψ := 56493/500000) 307 274
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t272 : ((45397207269/1000000000000 : ℚ) : ℝ) ≤ stT307 272 := by
  have hc : ((74871/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).1
  have hw2 : ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45397207269/1000000000000 : ℚ) : ℝ)
      = ((606339/10000000 : ℚ) : ℝ) * ((74871/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c273 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((460127/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 62823/625000) (δ := 15469/1000000000) (ψ := 56493/500000) 307 274
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t273 : ((278451022479/5000000000000 : ℚ) : ℝ) ≤ stT307 273 := by
  have hc : ((460077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).1
  have hw2 : ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((605227/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((278451022479/5000000000000 : ℚ) : ℝ)
      = ((605227/10000000 : ℚ) : ℝ) * ((460077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c274 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((23099/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 762291/2000000) (δ := 15469/1000000000) (ψ := 56493/500000) 307 274
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t274 : ((6962203989/2500000000000 : ℚ) : ℝ) ≤ stT307 274 := by
  have hc : ((23049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).1
  have hw2 : ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((302061/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6962203989/2500000000000 : ℚ) : ℝ)
      = ((302061/5000000 : ℚ) : ℝ) * ((23049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c275 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-878233/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 330369/500000) (δ := 7767/500000000) (ψ := 56493/500000) 307 274
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t275 : ((-529655000659/10000000000000 : ℚ) : ℝ) ≤ stT307 275 := by
  have hc : ((-878333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-529655000659/10000000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-878333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c276 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-163273/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6314711/10000000) (δ := 3869/250000000) (ψ := 56493/500000) 307 275
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t276 : ((-9829095549/200000000000 : ℚ) : ℝ) ≤ stT307 276 := by
  have hc : ((-163293/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).2
  have h0 : (0:ℝ) ≤ ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9829095549/200000000000 : ℚ) : ℝ)
      = ((60193/1000000 : ℚ) : ℝ) * ((-163293/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c277 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((19327/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1769447/5000000) (δ := 961/62500000) (ψ := 56493/500000) 307 275
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t277 : ((23209886989/2500000000000 : ℚ) : ℝ) ≤ stT307 277 := by
  have hc : ((38629/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23209886989/2500000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((38629/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c278 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((952561/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -773131/10000000) (δ := 961/62500000) (ψ := 56493/500000) 307 275
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t278 : ((7140600117/125000000000 : ℚ) : ℝ) ≤ stT307 278 := by
  have hc : ((952461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7140600117/125000000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((952461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c279 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((701667/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 991327/5000000) (δ := 15527/1000000000) (ψ := 56493/500000) 307 275
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t279 : ((105004234457/2500000000000 : ℚ) : ℝ) ≤ stT307 279 := by
  have hc : ((701567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).1
  have hw2 : ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149671/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105004234457/2500000000000 : ℚ) : ℝ)
      = ((149671/2500000 : ℚ) : ℝ) * ((701567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c280 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-315213/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4728693/10000000) (δ := 3869/250000000) (ψ := 56493/500000) 307 275
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t280 : ((-37687155699/2000000000000 : ℚ) : ℝ) ≤ stT307 280 := by
  have hc : ((-315313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37687155699/2000000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-315313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c281 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-987909/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 746483/1000000) (δ := 15427/1000000000) (ψ := 56493/500000) 307 275
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t281 : ((-11787935379/200000000000 : ℚ) : ℝ) ≤ stT307 281 := by
  have hc : ((-988009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11787935379/200000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-988009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c282 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-296939/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2758333/5000000) (δ := 15383/1000000000) (ψ := 56493/500000) 307 276
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t282 : ((-44213643397/1250000000000 : ℚ) : ℝ) ≤ stT307 282 := by
  have hc : ((-296989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).2
  have h0 : (0:ℝ) ≤ ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44213643397/1250000000000 : ℚ) : ℝ)
      = ((148873/2500000 : ℚ) : ℝ) * ((-296989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c283 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((435729/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -279987/1000000) (δ := 97/6250000) (ψ := 56493/500000) 307 276
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t283 : ((129477215751/5000000000000 : ℚ) : ℝ) ≤ stT307 283 := by
  have hc : ((435629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129477215751/5000000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((435629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c284 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((499657/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9259/1000000) (δ := 15383/1000000000) (ψ := 56493/500000) 307 276
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t284 : ((29646179773/500000000000 : ℚ) : ℝ) ≤ stT307 284 := by
  have hc : ((499607/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29646179773/500000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((499607/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c285 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((504461/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 325637/1250000) (δ := 15483/1000000000) (ψ := 56493/500000) 307 276
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t285 : ((74689307407/2500000000000 : ℚ) : ℝ) ≤ stT307 285 := by
  have hc : ((504361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).1
  have hw2 : ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((148087/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74689307407/2500000000000 : ℚ) : ℝ)
      = ((148087/2500000 : ℚ) : ℝ) * ((504361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c286 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-519761/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2646709/5000000) (δ := 15383/1000000000) (ψ := 56493/500000) 307 276
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t286 : ((-307400567493/10000000000000 : ℚ) : ℝ) ≤ stT307 286 := by
  have hc : ((-519861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-307400567493/10000000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-519861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c287 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-6243/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7735663/10000000) (δ := 1549/100000000) (ψ := 56493/500000) 307 277
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t287 : ((-14741997809/250000000000 : ℚ) : ℝ) ≤ stT307 287 := by
  have hc : ((-49949/50000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14741997809/250000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-49949/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c288 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-440057/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1013229/2000000) (δ := 15413/1000000000) (ψ := 56493/500000) 307 277
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t288 : ((-32420644149/1250000000000 : ℚ) : ℝ) ≤ stT307 288 := by
  have hc : ((-440157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).2
  have h0 : (0:ℝ) ≤ ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32420644149/1250000000000 : ℚ) : ℝ)
      = ((73657/1250000 : ℚ) : ℝ) * ((-440157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c289 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((285803/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -601459/2500000) (δ := 1549/100000000) (ψ := 56493/500000) 307 277
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t289 : ((33617983191/1000000000000 : ℚ) : ℝ) ≤ stT307 289 := by
  have hc : ((285753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33617983191/1000000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((285753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c290 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((995189/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 245339/10000000) (δ := 1539/100000000) (ψ := 56493/500000) 307 277
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t290 : ((29216808129/500000000000 : ℚ) : ℝ) ≤ stT307 290 := by
  have hc : ((995089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29216808129/500000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((995089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c291 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((40399/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 360913/1250000) (δ := 15413/1000000000) (ψ := 56493/500000) 307 277
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t291 : ((2367643569/100000000000 : ℚ) : ℝ) ≤ stT307 291 := by
  have hc : ((40389/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2367643569/100000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((40389/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c292 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-595043/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 552029/1000000) (δ := 1549/100000000) (ψ := 56493/500000) 307 277
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t292 : ((-174140627229/5000000000000 : ℚ) : ℝ) ≤ stT307 292 := by
  have hc : ((-595143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).2
  have h0 : (0:ℝ) ≤ ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174140627229/5000000000000 : ℚ) : ℝ)
      = ((292603/5000000 : ℚ) : ℝ) * ((-595143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c293 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-993269/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1512749/2000000) (δ := 7753/500000000) (ψ := 56493/500000) 307 278
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t293 : ((-580333123383/10000000000000 : ℚ) : ℝ) ≤ stT307 293 := by
  have hc : ((-993369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).2
  have h0 : (0:ℝ) ≤ ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-580333123383/10000000000000 : ℚ) : ℝ)
      = ((584207/10000000 : ℚ) : ℝ) * ((-993369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c294 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-397437/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -989759/2000000) (δ := 15497/1000000000) (ψ := 56493/500000) 307 278
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t294 : ((-57962087211/2500000000000 : ℚ) : ℝ) ≤ stT307 294 := by
  have hc : ((-397537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57962087211/2500000000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-397537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c295 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((592153/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -146417/625000) (δ := 15497/1000000000) (ψ := 56493/500000) 307 278
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t295 : ((172353140883/5000000000000 : ℚ) : ℝ) ≤ stT307 295 := by
  have hc : ((592053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).1
  have hw2 : ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((291111/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172353140883/5000000000000 : ℚ) : ℝ)
      = ((291111/5000000 : ℚ) : ℝ) * ((592053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c296 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((497409/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7957/312500) (δ := 7753/500000000) (ψ := 56493/500000) 307 278
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t296 : ((144541975221/2500000000000 : ℚ) : ℝ) ≤ stT307 296 := by
  have hc : ((497359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).1
  have hw2 : ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144541975221/2500000000000 : ℚ) : ℝ)
      = ((290619/5000000 : ℚ) : ℝ) * ((497359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c297 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((16803/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 710793/2500000) (δ := 15497/1000000000) (ψ := 56493/500000) 307 278
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t297 : ((4873877071/200000000000 : ℚ) : ℝ) ≤ stT307 297 := by
  have hc : ((16799/40000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).1
  have hw2 : ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290129/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4873877071/200000000000 : ℚ) : ℝ)
      = ((290129/5000000 : ℚ) : ℝ) * ((16799/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c298 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-281657/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5422969/10000000) (δ := 7753/500000000) (ψ := 56493/500000) 307 278
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t298 : ((-32637727899/1000000000000 : ℚ) : ℝ) ≤ stT307 298 := by
  have hc : ((-281707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).2
  have h0 : (0:ℝ) ≤ ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32637727899/1000000000000 : ℚ) : ℝ)
      = ((115857/2000000 : ℚ) : ℝ) * ((-281707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c299 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-249607/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -60264/78125) (δ := 3081/200000000) (ψ := 56493/500000) 307 279
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t299 : ((-902287063/15625000000 : ℚ) : ℝ) ≤ stT307 299 := by
  have hc : ((-15602/15625 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).2
  have h0 : (0:ℝ) ≤ ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-902287063/15625000000 : ℚ) : ℝ)
      = ((115663/2000000 : ℚ) : ℝ) * ((-15602/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c300 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-235171/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2575593/5000000) (δ := 3101/200000000) (ψ := 56493/500000) 307 279
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t300 : ((-135805079571/5000000000000 : ℚ) : ℝ) ≤ stT307 300 := by
  have hc : ((-235221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).2
  have h0 : (0:ℝ) ≤ ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135805079571/5000000000000 : ℚ) : ℝ)
      = ((577351/10000000 : ℚ) : ℝ) * ((-235221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c301 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((25361/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25971/100000) (δ := 7699/500000000) (ψ := 56493/500000) 307 279
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t301 : ((365373621/12500000000 : ℚ) : ℝ) ≤ stT307 301 := by
  have hc : ((6339/12500 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).1
  have hw2 : ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57639/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((365373621/12500000000 : ℚ) : ℝ)
      = ((57639/1000000 : ℚ) : ℝ) * ((6339/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c302 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((249947/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -402/78125) (δ := 7699/500000000) (ψ := 56493/500000) 307 279
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t302 : ((14381386607/250000000000 : ℚ) : ℝ) ≤ stT307 302 := by
  have hc : ((124961/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).1
  have hw2 : ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((115087/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14381386607/250000000000 : ℚ) : ℝ)
      = ((115087/2000000 : ℚ) : ℝ) * ((124961/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c303 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((545091/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1242873/5000000) (δ := 3101/200000000) (ψ := 56493/500000) 307 279
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t303 : ((78272152411/2500000000000 : ℚ) : ℝ) ≤ stT307 303 := by
  have hc : ((544991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).1
  have hw2 : ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143621/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78272152411/2500000000000 : ℚ) : ℝ)
      = ((143621/2500000 : ℚ) : ℝ) * ((544991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c304 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-421443/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5014581/10000000) (δ := 7749/500000000) (ψ := 56493/500000) 307 279
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t304 : ((-12088588611/500000000000 : ℚ) : ℝ) ≤ stT307 304 := by
  have hc : ((-421543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12088588611/500000000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-421543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c305 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-495937/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7535051/10000000) (δ := 7749/500000000) (ψ := 56493/500000) 307 279
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t305 : ((-284001660213/5000000000000 : ℚ) : ℝ) ≤ stT307 305 := by
  have hc : ((-495987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).2
  have h0 : (0:ℝ) ≤ ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284001660213/5000000000000 : ℚ) : ℝ)
      = ((572599/10000000 : ℚ) : ℝ) * ((-495987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c306 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-319591/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5660577/10000000) (δ := 1939/125000000) (ψ := 56493/500000) 307 280
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t306 : ((-91363306671/2500000000000 : ℚ) : ℝ) ≤ stT307 306 := by
  have hc : ((-319641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).2
  have h0 : (0:ℝ) ≤ ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91363306671/2500000000000 : ℚ) : ℝ)
      = ((285831/5000000 : ℚ) : ℝ) * ((-319641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c307 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((9479/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -789133/2500000) (δ := 15391/1000000000) (ψ := 56493/500000) 307 280
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t307 : ((4326532911/250000000000 : ℚ) : ℝ) ≤ stT307 307 := by
  have hc : ((75807/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4326532911/250000000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((75807/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c308 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((965289/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -330311/5000000) (δ := 15391/1000000000) (ψ := 56493/500000) 307 280
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t308 : ((274983311289/5000000000000 : ℚ) : ℝ) ≤ stT307 308 := by
  have hc : ((965189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274983311289/5000000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((965189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c309 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((37229/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1827229/10000000) (δ := 15491/1000000000) (ψ := 56493/500000) 307 280
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t309 : ((33087483/781250000 : ℚ) : ℝ) ≤ stT307 309 := by
  have hc : ((4653/6250 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33087483/781250000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((4653/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c310 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-37857/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2153511/5000000) (δ := 3853/250000000) (ψ := 56493/500000) 307 280
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t310 : ((-5378884121/625000000000 : ℚ) : ℝ) ≤ stT307 310 := by
  have hc : ((-18941/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5378884121/625000000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-18941/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c311 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-454477/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6778909/10000000) (δ := 15391/1000000000) (ψ := 56493/500000) 307 280
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t311 : ((-32217328287/625000000000 : ℚ) : ℝ) ≤ stT307 311 := by
  have hc : ((-454527/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32217328287/625000000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-454527/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c312 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-212409/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3232613/5000000) (δ := 3871/250000000) (ψ := 56493/500000) 307 281
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t312 : ((-60133586163/1250000000000 : ℚ) : ℝ) ≤ stT307 312 := by
  have hc : ((-106217/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60133586163/1250000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-106217/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c313 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-4111/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2004613/5000000) (δ := 3871/250000000) (ψ := 56493/500000) 307 281
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t313 : ((-2330742399/1250000000000 : ℚ) : ℝ) ≤ stT307 313 := by
  have hc : ((-8247/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2330742399/1250000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-8247/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c314 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((811301/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -780527/5000000) (δ := 15419/1000000000) (ψ := 56493/500000) 307 281
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t314 : ((114446670683/2500000000000 : ℚ) : ℝ) ≤ stT307 314 := by
  have hc : ((811201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).1
  have hw2 : ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141083/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114446670683/2500000000000 : ℚ) : ℝ)
      = ((141083/2500000 : ℚ) : ℝ) * ((811201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c315 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((234693/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 439683/5000000) (δ := 15519/1000000000) (ψ := 56493/500000) 307 281
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t315 : ((8263774953/156250000000 : ℚ) : ℝ) ≤ stT307 315 := by
  have hc : ((58667/62500 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8263774953/156250000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((58667/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c316 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((24351/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1656017/5000000) (δ := 15519/1000000000) (ψ := 56493/500000) 307 281
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t316 : ((13692859163/1000000000000 : ℚ) : ℝ) ≤ stT307 316 := by
  have hc : ((24341/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13692859163/1000000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((24341/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c317 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-331187/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 114739/200000) (δ := 15419/1000000000) (ψ := 56493/500000) 307 281
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t317 : ((-23255156059/625000000000 : ℚ) : ℝ) ≤ stT307 317 := by
  have hc : ((-331237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).2
  have h0 : (0:ℝ) ≤ ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23255156059/625000000000 : ℚ) : ℝ)
      = ((70207/1250000 : ℚ) : ℝ) * ((-331237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c318 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-198559/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1510739/2000000) (δ := 7763/500000000) (ψ := 56493/500000) 307 282
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t318 : ((-111357741567/2000000000000 : ℚ) : ℝ) ≤ stT307 318 := by
  have hc : ((-198579/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).2
  have h0 : (0:ℝ) ≤ ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111357741567/2000000000000 : ℚ) : ℝ)
      = ((560773/10000000 : ℚ) : ℝ) * ((-198579/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c319 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-58471/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5143899/10000000) (δ := 15377/1000000000) (ψ := 56493/500000) 307 282
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t319 : ((-65489004531/2500000000000 : ℚ) : ℝ) ≤ stT307 319 := by
  have hc : ((-116967/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65489004531/2500000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-116967/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c320 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((18261/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2741777/10000000) (δ := 7763/500000000) (ψ := 56493/500000) 307 282
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t320 : ((1275744389/50000000000 : ℚ) : ℝ) ≤ stT307 320 := by
  have hc : ((18257/40000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).1
  have hw2 : ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69877/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1275744389/50000000000 : ℚ) : ℝ)
      = ((69877/1250000 : ℚ) : ℝ) * ((18257/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c321 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((990381/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21689/625000) (δ := 15377/1000000000) (ψ := 56493/500000) 307 282
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t321 : ((110544077749/2000000000000 : ℚ) : ℝ) ≤ stT307 321 := by
  have hc : ((990281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).1
  have hw2 : ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111629/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110544077749/2000000000000 : ℚ) : ℝ)
      = ((111629/2000000 : ℚ) : ℝ) * ((990281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c322 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((17127/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 127513/625000) (δ := 15377/1000000000) (ψ := 56493/500000) 307 282
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t322 : ((9543107111/250000000000 : ℚ) : ℝ) ≤ stT307 322 := by
  have hc : ((34249/50000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9543107111/250000000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((34249/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c323 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-48989/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 552509/1250000) (δ := 15377/1000000000) (ψ := 56493/500000) 307 282
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t323 : ((-2727212481/250000000000 : ℚ) : ℝ) ≤ stT307 323 := by
  have hc : ((-24507/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).2
  have h0 : (0:ℝ) ≤ ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2727212481/250000000000 : ℚ) : ℝ)
      = ((111283/2000000 : ℚ) : ℝ) * ((-24507/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c324 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-455609/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 849071/1250000) (δ := 15377/1000000000) (ψ := 56493/500000) 307 282
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t324 : ((-63286022851/1250000000000 : ℚ) : ℝ) ≤ stT307 324 := by
  have hc : ((-455659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).2
  have h0 : (0:ℝ) ≤ ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63286022851/1250000000000 : ℚ) : ℝ)
      = ((138889/2500000 : ℚ) : ℝ) * ((-455659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c325 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-21677/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6550267/10000000) (δ := 15433/1000000000) (ψ := 56493/500000) 307 283
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t325 : ((-24051280659/500000000000 : ℚ) : ℝ) ≤ stT307 325 := by
  have hc : ((-43359/50000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).2
  have h0 : (0:ℝ) ≤ ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24051280659/500000000000 : ℚ) : ℝ)
      = ((554701/10000000 : ℚ) : ℝ) * ((-43359/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c326 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-52973/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2096177/5000000) (δ := 1547/100000000) (ψ := 56493/500000) 307 283
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t326 : ((-29366735527/5000000000000 : ℚ) : ℝ) ≤ stT307 326 := by
  have hc : ((-53023/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).2
  have h0 : (0:ℝ) ≤ ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29366735527/5000000000000 : ℚ) : ℝ)
      = ((553849/10000000 : ℚ) : ℝ) * ((-53023/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c327 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((148143/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -368331/2000000) (δ := 1547/100000000) (ψ := 56493/500000) 307 283
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t327 : ((81912167123/2000000000000 : ℚ) : ℝ) ≤ stT307 327 := by
  have hc : ((148123/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).1
  have hw2 : ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((553001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81912167123/2000000000000 : ℚ) : ℝ)
      = ((553001/10000000 : ℚ) : ℝ) * ((148123/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c328 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((195983/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 501907/10000000) (δ := 15533/1000000000) (ψ := 56493/500000) 307 283
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t328 : ((108202342191/2000000000000 : ℚ) : ℝ) ≤ stT307 328 := by
  have hc : ((195963/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).1
  have hw2 : ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((552157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108202342191/2000000000000 : ℚ) : ℝ)
      = ((552157/10000000 : ℚ) : ℝ) * ((195963/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c329 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((421859/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2838253/10000000) (δ := 1547/100000000) (ψ := 56493/500000) 307 283
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t329 : ((232522906603/10000000000000 : ℚ) : ℝ) ≤ stT307 329 := by
  have hc : ((421759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).1
  have hw2 : ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((551317/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((232522906603/10000000000000 : ℚ) : ℝ)
      = ((551317/10000000 : ℚ) : ℝ) * ((421759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c330 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-59513/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5167539/10000000) (δ := 1537/100000000) (ψ := 56493/500000) 307 283
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t330 : ((-32767716291/1250000000000 : ℚ) : ℝ) ≤ stT307 330 := by
  have hc : ((-119051/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).2
  have h0 : (0:ℝ) ≤ ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32767716291/1250000000000 : ℚ) : ℝ)
      = ((275241/5000000 : ℚ) : ℝ) * ((-119051/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c331 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-494703/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1872441/2500000) (δ := 15433/1000000000) (ψ := 56493/500000) 307 283
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t331 : ((-5438819729/100000000000 : ℚ) : ℝ) ≤ stT307 331 := by
  have hc : ((-494753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5438819729/100000000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-494753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c332 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-355313/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5902959/10000000) (δ := 7681/500000000) (ψ := 56493/500000) 307 284
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t332 : ((-97515516193/2500000000000 : ℚ) : ℝ) ≤ stT307 332 := by
  have hc : ((-355363/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).2
  have h0 : (0:ℝ) ≤ ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97515516193/2500000000000 : ℚ) : ℝ)
      = ((274411/5000000 : ℚ) : ℝ) * ((-355363/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c333 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((33131/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3594703/10000000) (δ := 7731/500000000) (ψ := 56493/500000) 307 284
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t333 : ((2267744447/312500000000 : ℚ) : ℝ) ≤ stT307 333 := by
  have hc : ((16553/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2267744447/312500000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((16553/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c334 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((869137/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -646677/5000000) (δ := 7681/500000000) (ψ := 56493/500000) 307 284
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t334 : ((19020612819/400000000000 : ℚ) : ℝ) ≤ stT307 334 := by
  have hc : ((869037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19020612819/400000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((869037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c335 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((11511/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 250291/2500000) (δ := 7681/500000000) (ψ := 56493/500000) 307 284
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t335 : ((12576887981/250000000000 : ℚ) : ℝ) ≤ stT307 335 := by
  have hc : ((46039/50000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12576887981/250000000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((46039/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c336 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((126261/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 131551/400000) (δ := 15541/1000000000) (ψ := 56493/500000) 307 284
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t336 : ((8606706723/625000000000 : ℚ) : ℝ) ≤ stT307 336 := by
  have hc : ((126211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8606706723/625000000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((126211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c337 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-610789/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5569631/10000000) (δ := 7681/500000000) (ψ := 56493/500000) 307 284
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t337 : ((-66554523883/2000000000000 : ℚ) : ℝ) ≤ stT307 337 := by
  have hc : ((-610889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).2
  have h0 : (0:ℝ) ≤ ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66554523883/2000000000000 : ℚ) : ℝ)
      = ((108947/2000000 : ℚ) : ℝ) * ((-610889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c338 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-999991/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7843657/10000000) (δ := 15441/1000000000) (ψ := 56493/500000) 307 284
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t338 : ((-543978497539/10000000000000 : ℚ) : ℝ) ≤ stT307 338 := by
  have hc : ((-1000091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).2
  have h0 : (0:ℝ) ≤ ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-543978497539/10000000000000 : ℚ) : ℝ)
      = ((543929/10000000 : ℚ) : ℝ) * ((-1000091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c339 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-619383/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5596881/10000000) (δ := 1931/125000000) (ψ := 56493/500000) 307 285
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t339 : ((-168228661929/5000000000000 : ℚ) : ℝ) ≤ stT307 339 := by
  have hc : ((-619483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168228661929/5000000000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-619483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c340 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((234119/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -333621/1000000) (δ := 3071/200000000) (ψ := 56493/500000) 307 285
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t340 : ((63457294097/5000000000000 : ℚ) : ℝ) ≤ stT307 340 := by
  have hc : ((234019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).1
  have hw2 : ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63457294097/5000000000000 : ℚ) : ℝ)
      = ((271163/5000000 : ℚ) : ℝ) * ((234019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c341 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((907759/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -135277/1250000) (δ := 3071/200000000) (ψ := 56493/500000) 307 285
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t341 : ((49152457827/1000000000000 : ℚ) : ℝ) ≤ stT307 341 := by
  have hc : ((907659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).1
  have hw2 : ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((54153/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49152457827/1000000000000 : ℚ) : ℝ)
      = ((54153/1000000 : ℚ) : ℝ) * ((907659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c342 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((893327/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 582627/5000000) (δ := 3091/200000000) (ψ := 56493/500000) 307 285
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t342 : ((241500890763/5000000000000 : ℚ) : ℝ) ≤ stT307 342 := by
  have hc : ((893227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).1
  have hw2 : ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((270369/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((241500890763/5000000000000 : ℚ) : ℝ)
      = ((270369/5000000 : ℚ) : ℝ) * ((893227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c343 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((206843/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 851531/2500000) (δ := 3071/200000000) (ψ := 56493/500000) 307 285
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t343 : ((111630676107/10000000000000 : ℚ) : ℝ) ≤ stT307 343 := by
  have hc : ((206743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111630676107/10000000000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((206743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c344 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-39561/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 564047/1000000) (δ := 3071/200000000) (ψ := 56493/500000) 307 285
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t344 : ((-21333236779/625000000000 : ℚ) : ℝ) ≤ stT307 344 := by
  have hc : ((-158269/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).2
  have h0 : (0:ℝ) ≤ ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21333236779/625000000000 : ℚ) : ℝ)
      = ((134791/2500000 : ℚ) : ℝ) * ((-158269/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c345 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-999983/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3919797/5000000) (δ := 3091/200000000) (ψ := 56493/500000) 307 286
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t345 : ((-269213342853/5000000000000 : ℚ) : ℝ) ≤ stT307 345 := by
  have hc : ((-1000083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).2
  have h0 : (0:ℝ) ≤ ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-269213342853/5000000000000 : ℚ) : ℝ)
      = ((269191/5000000 : ℚ) : ℝ) * ((-1000083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c346 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-626061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5618219/10000000) (δ := 3071/200000000) (ψ := 56493/500000) 307 286
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t346 : ((-84156664561/2500000000000 : ℚ) : ℝ) ≤ stT307 346 := by
  have hc : ((-626161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).2
  have h0 : (0:ℝ) ≤ ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84156664561/2500000000000 : ℚ) : ℝ)
      = ((134401/2500000 : ℚ) : ℝ) * ((-626161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c347 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((207981/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1701607/5000000) (δ := 3071/200000000) (ψ := 56493/500000) 307 286
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t347 : ((27899085367/2500000000000 : ℚ) : ℝ) ≤ stT307 347 := by
  have hc : ((207881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27899085367/2500000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((207881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c348 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((443997/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1194579/10000000) (δ := 3091/200000000) (ψ := 56493/500000) 307 286
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t348 : ((29747556629/625000000000 : ℚ) : ℝ) ≤ stT307 348 := by
  have hc : ((443947/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).1
  have hw2 : ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29747556629/625000000000 : ℚ) : ℝ)
      = ((67007/1250000 : ℚ) : ℝ) * ((443947/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c349 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((919847/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 503881/5000000) (δ := 3071/200000000) (ψ := 56493/500000) 307 286
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t349 : ((492328612389/10000000000000 : ℚ) : ℝ) ≤ stT307 349 := by
  have hc : ((919747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).1
  have hw2 : ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((535287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((492328612389/10000000000000 : ℚ) : ℝ)
      = ((535287/10000000 : ℚ) : ℝ) * ((919747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c350 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((71321/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3203733/10000000) (δ := 3071/200000000) (ψ := 56493/500000) 307 286
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t350 : ((148864377/9765625000 : ℚ) : ℝ) ≤ stT307 350 := by
  have hc : ((4456/15625 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).1
  have hw2 : ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((267261/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148864377/9765625000 : ℚ) : ℝ)
      = ((267261/5000000 : ℚ) : ℝ) * ((4456/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c351 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-553531/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5393487/10000000) (δ := 1931/125000000) (ψ := 56493/500000) 307 286
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t351 : ((-295506636191/10000000000000 : ℚ) : ℝ) ≤ stT307 351 := by
  have hc : ((-553631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-295506636191/10000000000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-553631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c352 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-496933/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1894237/2500000) (δ := 3071/200000000) (ψ := 56493/500000) 307 286
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t352 : ((-132446466483/2500000000000 : ℚ) : ℝ) ≤ stT307 352 := by
  have hc : ((-496983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132446466483/2500000000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-496983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c353 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-724757/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1190739/2000000) (δ := 15541/1000000000) (ψ := 56493/500000) 307 287
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t353 : ((-385802963679/10000000000000 : ℚ) : ℝ) ≤ stT307 353 := by
  have hc : ((-724857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).2
  have h0 : (0:ℝ) ≤ ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-385802963679/10000000000000 : ℚ) : ℝ)
      = ((532247/10000000 : ℚ) : ℝ) * ((-724857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c354 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((57759/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1891257/5000000) (δ := 15441/1000000000) (ψ := 56493/500000) 307 287
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t354 : ((15322706273/5000000000000 : ℚ) : ℝ) ≤ stT307 354 := by
  have hc : ((57659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).1
  have hw2 : ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((265747/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15322706273/5000000000000 : ℚ) : ℝ)
      = ((265747/5000000 : ℚ) : ℝ) * ((57659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c355 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((199471/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32351/200000) (δ := 15441/1000000000) (ψ := 56493/500000) 307 287
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t355 : ((6615922989/156250000000 : ℚ) : ℝ) ≤ stT307 355 := by
  have hc : ((99723/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).1
  have hw2 : ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66343/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6615922989/156250000000 : ℚ) : ℝ)
      = ((66343/1250000 : ℚ) : ℝ) * ((99723/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c356 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((3052/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 135357/2500000) (δ := 7731/500000000) (ψ := 56493/500000) 307 287
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t356 : ((12939106173/250000000000 : ℚ) : ℝ) ≤ stT307 356 := by
  have hc : ((48827/50000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).1
  have hw2 : ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((264999/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12939106173/250000000000 : ℚ) : ℝ)
      = ((264999/5000000 : ℚ) : ℝ) * ((48827/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c357 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((9467/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 538853/2000000) (δ := 15441/1000000000) (ψ := 56493/500000) 307 287
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t357 : ((125235201/5000000000 : ℚ) : ℝ) ≤ stT307 357 := by
  have hc : ((1893/4000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).1
  have hw2 : ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66157/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125235201/5000000000 : ℚ) : ℝ)
      = ((66157/1250000 : ℚ) : ℝ) * ((1893/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c358 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-89389/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1210279/2500000) (δ := 15441/1000000000) (ψ := 56493/500000) 307 287
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t358 : ((-23628409519/1250000000000 : ℚ) : ℝ) ≤ stT307 358 := by
  have hc : ((-44707/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).2
  have h0 : (0:ℝ) ≤ ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23628409519/1250000000000 : ℚ) : ℝ)
      = ((528517/10000000 : ℚ) : ℝ) * ((-44707/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c359 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-939783/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6981981/10000000) (δ := 7731/500000000) (ψ := 56493/500000) 307 287
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t359 : ((-24802572487/500000000000 : ℚ) : ℝ) ≤ stT307 359 := by
  have hc : ((-939883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).2
  have h0 : (0:ℝ) ≤ ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24802572487/500000000000 : ℚ) : ℝ)
      = ((26389/500000 : ℚ) : ℝ) * ((-939883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c360 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-875087/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1647757/2500000) (δ := 7717/500000000) (ψ := 56493/500000) 307 288
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t360 : ((-461264682789/10000000000000 : ℚ) : ℝ) ≤ stT307 360 := by
  have hc : ((-875187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).2
  have h0 : (0:ℝ) ≤ ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-461264682789/10000000000000 : ℚ) : ℝ)
      = ((527047/10000000 : ℚ) : ℝ) * ((-875187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c361 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-212397/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -223103/500000) (δ := 7767/500000000) (ψ := 56493/500000) 307 288
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t361 : ((-27960142763/2500000000000 : ℚ) : ℝ) ≤ stT307 361 := by
  have hc : ((-212497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).2
  have h0 : (0:ℝ) ≤ ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27960142763/2500000000000 : ℚ) : ℝ)
      = ((131579/2500000 : ℚ) : ℝ) * ((-212497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c362 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((7417/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -584731/2500000) (δ := 15469/1000000000) (ψ := 56493/500000) 307 288
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t362 : ((3897629211/125000000000 : ℚ) : ℝ) ≤ stT307 362 := by
  have hc : ((29663/50000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3897629211/125000000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((29663/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c363 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((996071/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -221699/10000000) (δ := 7717/500000000) (ψ := 56493/500000) 307 288
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t363 : ((522748326973/10000000000000 : ℚ) : ℝ) ≤ stT307 363 := by
  have hc : ((995971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).1
  have hw2 : ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((524863/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((522748326973/10000000000000 : ℚ) : ℝ)
      = ((524863/10000000 : ℚ) : ℝ) * ((995971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c364 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((72767/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 944847/5000000) (δ := 15469/1000000000) (ψ := 56493/500000) 307 288
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t364 : ((19067499747/500000000000 : ℚ) : ℝ) ≤ stT307 364 := by
  have hc : ((72757/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).1
  have hw2 : ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19067499747/500000000000 : ℚ) : ℝ)
      = ((262071/5000000 : ℚ) : ℝ) * ((72757/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c365 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-6833/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 399533/1000000) (δ := 15369/1000000000) (ψ := 56493/500000) 307 288
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t365 : ((-56088153/39062500000 : ℚ) : ℝ) ≤ stT307 365 := by
  have hc : ((-3429/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56088153/39062500000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-3429/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c366 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-762577/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 609521/1000000) (δ := 15369/1000000000) (ψ := 56493/500000) 307 288
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t366 : ((-398658131993/10000000000000 : ℚ) : ℝ) ≤ stT307 366 := by
  have hc : ((-762677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-398658131993/10000000000000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-762677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c367 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-991017/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -751863/1000000) (δ := 15527/1000000000) (ψ := 56493/500000) 307 289
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t367 : ((-129339777383/2500000000000 : ℚ) : ℝ) ≤ stT307 367 := by
  have hc : ((-991117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129339777383/2500000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-991117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c368 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-565697/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1086037/2000000) (δ := 3869/250000000) (ψ := 56493/500000) 307 289
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t368 : ((-294942620739/10000000000000 : ℚ) : ℝ) ≤ stT307 368 := by
  have hc : ((-565797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).2
  have h0 : (0:ℝ) ≤ ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-294942620739/10000000000000 : ℚ) : ℝ)
      = ((521287/10000000 : ℚ) : ℝ) * ((-565797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c369 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((229757/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3347421/10000000) (δ := 15527/1000000000) (ψ := 56493/500000) 307 289
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t369 : ((119554611403/10000000000000 : ℚ) : ℝ) ≤ stT307 369 := by
  have hc : ((229657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119554611403/10000000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((229657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c370 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((873669/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1270259/10000000) (δ := 15527/1000000000) (ψ := 56493/500000) 307 289
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t370 : ((3633173471/80000000000 : ℚ) : ℝ) ≤ stT307 370 := by
  have hc : ((873569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).1
  have hw2 : ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((4159/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3633173471/80000000000 : ℚ) : ℝ)
      = ((4159/80000 : ℚ) : ℝ) * ((873569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c371 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((949081/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 100153/1250000) (δ := 961/62500000) (ψ := 56493/500000) 307 289
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t371 : ((246343130847/5000000000000 : ℚ) : ℝ) ≤ stT307 371 := by
  have hc : ((948981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).1
  have hw2 : ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((259587/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((246343130847/5000000000000 : ℚ) : ℝ)
      = ((259587/5000000 : ℚ) : ℝ) * ((948981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c372 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((411341/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143359/500000) (δ := 15527/1000000000) (ψ := 56493/500000) 307 289
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t372 : ((8528727099/400000000000 : ℚ) : ℝ) ≤ stT307 372 := by
  have hc : ((411241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).1
  have hw2 : ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((20739/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8528727099/400000000000 : ℚ) : ℝ)
      = ((20739/400000 : ℚ) : ℝ) * ((411241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c373 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-389647/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4927611/10000000) (δ := 961/62500000) (ψ := 56493/500000) 307 289
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t373 : ((-201803591407/10000000000000 : ℚ) : ℝ) ≤ stT307 373 := by
  have hc : ((-389747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).2
  have h0 : (0:ℝ) ≤ ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-201803591407/10000000000000 : ℚ) : ℝ)
      = ((517781/10000000 : ℚ) : ℝ) * ((-389747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c374 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-469923/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6982439/10000000) (δ := 3869/250000000) (ψ := 56493/500000) 307 289
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t374 : ((-7594293707/156250000000 : ℚ) : ℝ) ≤ stT307 374 := by
  have hc : ((-469973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7594293707/156250000000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-469973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c375 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-5569/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6676069/10000000) (δ := 3871/250000000) (ψ := 56493/500000) 307 290
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t375 : ((-11504572843/250000000000 : ℚ) : ℝ) ≤ stT307 375 := by
  have hc : ((-44557/50000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).2
  have h0 : (0:ℝ) ≤ ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11504572843/250000000000 : ℚ) : ℝ)
      = ((258199/5000000 : ℚ) : ℝ) * ((-44557/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c376 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-55667/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -231607/500000) (δ := 1923/125000000) (ψ := 56493/500000) 307 290
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t376 : ((-28718398457/2000000000000 : ℚ) : ℝ) ≤ stT307 376 := by
  have hc : ((-55687/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).2
  have h0 : (0:ℝ) ≤ ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28718398457/2000000000000 : ℚ) : ℝ)
      = ((515711/10000000 : ℚ) : ℝ) * ((-55687/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c377 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((254203/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -129683/500000) (δ := 1923/125000000) (ψ := 56493/500000) 307 290
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t377 : ((65447701489/2500000000000 : ℚ) : ℝ) ≤ stT307 377 := by
  have hc : ((254153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65447701489/2500000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((254153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c378 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((121871/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -560553/10000000) (δ := 15519/1000000000) (ψ := 56493/500000) 307 290
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t378 : ((15669297081/312500000000 : ℚ) : ℝ) ≤ stT307 378 := by
  have hc : ((243717/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15669297081/312500000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((243717/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c379 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((832659/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1467259/10000000) (δ := 15419/1000000000) (ψ := 56493/500000) 307 290
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t379 : ((85531283747/2000000000000 : ℚ) : ℝ) ≤ stT307 379 := by
  have hc : ((832559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).1
  have hw2 : ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102733/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85531283747/2000000000000 : ℚ) : ℝ)
      = ((102733/2000000 : ℚ) : ℝ) * ((832559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c380 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((21757/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1744811/5000000) (δ := 3871/250000000) (ψ := 56493/500000) 307 290
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t380 : ((22309378621/2500000000000 : ℚ) : ℝ) ≤ stT307 380 := by
  have hc : ((43489/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).1
  have hw2 : ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22309378621/2500000000000 : ℚ) : ℝ)
      = ((512989/10000000 : ℚ) : ℝ) * ((43489/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c381 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-295331/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 43021/78125) (δ := 15519/1000000000) (ψ := 56493/500000) 307 290
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t381 : ((-37832103099/1250000000000 : ℚ) : ℝ) ≤ stT307 381 := by
  have hc : ((-295381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37832103099/1250000000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-295381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c382 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-247753/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 939817/1250000) (δ := 15419/1000000000) (ψ := 56493/500000) 307 290
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t382 : ((-12677437481/250000000000 : ℚ) : ℝ) ≤ stT307 382 := by
  have hc : ((-123889/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).2
  have h0 : (0:ℝ) ≤ ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12677437481/250000000000 : ℚ) : ℝ)
      = ((102329/2000000 : ℚ) : ℝ) * ((-123889/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c383 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-784807/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -772869/1250000) (δ := 3853/250000000) (ψ := 56493/500000) 307 291
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t383 : ((-401069424139/10000000000000 : ℚ) : ℝ) ≤ stT307 383 := by
  have hc : ((-784907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).2
  have h0 : (0:ℝ) ≤ ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-401069424139/10000000000000 : ℚ) : ℝ)
      = ((510977/10000000 : ℚ) : ℝ) * ((-784907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c384 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-4067/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4181619/10000000) (δ := 3853/250000000) (ψ := 56493/500000) 307 291
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t384 : ((-2077476081/400000000000 : ℚ) : ℝ) ≤ stT307 384 := by
  have hc : ((-4071/40000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).2
  have h0 : (0:ℝ) ≤ ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2077476081/400000000000 : ℚ) : ℝ)
      = ((510311/10000000 : ℚ) : ℝ) * ((-4071/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c385 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((641609/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -437101/2000000) (δ := 3853/250000000) (ψ := 56493/500000) 307 291
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t385 : ((326943137323/10000000000000 : ℚ) : ℝ) ≤ stT307 385 := by
  have hc : ((641509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((326943137323/10000000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((641509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c386 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((249243/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19461/1000000) (δ := 3853/250000000) (ψ := 56493/500000) 307 291
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t386 : ((31712118237/625000000000 : ℚ) : ℝ) ≤ stT307 386 := by
  have hc : ((124609/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).1
  have hw2 : ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((254493/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31712118237/625000000000 : ℚ) : ℝ)
      = ((254493/5000000 : ℚ) : ℝ) * ((124609/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c387 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((754137/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1791143/10000000) (δ := 15391/1000000000) (ψ := 56493/500000) 307 291
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t387 : ((47912265017/1250000000000 : ℚ) : ℝ) ≤ stT307 387 := by
  have hc : ((754037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).1
  have hw2 : ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((63541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47912265017/1250000000000 : ℚ) : ℝ)
      = ((63541/1250000 : ℚ) : ℝ) * ((754037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c388 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((7753/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 377183/1000000) (δ := 3853/250000000) (ψ := 56493/500000) 307 291
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t388 : ((7859285713/2500000000000 : ℚ) : ℝ) ≤ stT307 388 := by
  have hc : ((15481/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).1
  have hw2 : ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7859285713/2500000000000 : ℚ) : ℝ)
      = ((507673/10000000 : ℚ) : ℝ) * ((15481/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c389 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-665493/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45979/80000) (δ := 3853/250000000) (ψ := 56493/500000) 307 291
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t389 : ((-337469628453/10000000000000 : ℚ) : ℝ) ≤ stT307 389 := by
  have hc : ((-665593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-337469628453/10000000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-665593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c390 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-499259/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1543571/2000000) (δ := 15491/1000000000) (ψ := 56493/500000) 307 291
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t390 : ((-25283509833/500000000000 : ℚ) : ℝ) ≤ stT307 390 := by
  have hc : ((-499309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).2
  have h0 : (0:ℝ) ≤ ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25283509833/500000000000 : ℚ) : ℝ)
      = ((50637/1000000 : ℚ) : ℝ) * ((-499309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c391 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-74403/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1204939/2000000) (δ := 3101/200000000) (ψ := 56493/500000) 307 292
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t391 : ((-18816145593/500000000000 : ℚ) : ℝ) ≤ stT307 391 := by
  have hc : ((-74413/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).2
  have h0 : (0:ℝ) ≤ ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18816145593/500000000000 : ℚ) : ℝ)
      = ((252861/5000000 : ℚ) : ℝ) * ((-74413/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c392 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-13721/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4064269/10000000) (δ := 7749/500000000) (ψ := 56493/500000) 307 292
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t392 : ((-3471394221/1250000000000 : ℚ) : ℝ) ≤ stT307 392 := by
  have hc : ((-6873/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).2
  have h0 : (0:ℝ) ≤ ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3471394221/1250000000000 : ℚ) : ℝ)
      = ((505077/10000000 : ℚ) : ℝ) * ((-6873/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c393 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((166207/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2108833/10000000) (δ := 3081/200000000) (ψ := 56493/500000) 307 292
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t393 : ((41913842403/1250000000000 : ℚ) : ℝ) ≤ stT307 393 := by
  have hc : ((83091/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41913842403/1250000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((83091/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c394 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((498997/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -31677/2000000) (δ := 7699/500000000) (ψ := 56493/500000) 307 292
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t394 : ((15710344189/312500000000 : ℚ) : ℝ) ≤ stT307 394 := by
  have hc : ((498947/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).1
  have hw2 : ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31487/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15710344189/312500000000 : ℚ) : ℝ)
      = ((31487/625000 : ℚ) : ℝ) * ((498947/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c395 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((151041/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 893537/5000000) (δ := 7699/500000000) (ψ := 56493/500000) 307 292
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t395 : ((37993410117/1000000000000 : ℚ) : ℝ) ≤ stT307 395 := by
  have hc : ((151021/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).1
  have hw2 : ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37993410117/1000000000000 : ℚ) : ℝ)
      = ((251577/5000000 : ℚ) : ℝ) * ((151021/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c396 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((79633/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1863849/5000000) (δ := 7749/500000000) (ψ := 56493/500000) 307 292
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t396 : ((19983382047/5000000000000 : ℚ) : ℝ) ≤ stT307 396 := by
  have hc : ((79533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).1
  have hw2 : ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251259/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19983382047/5000000000000 : ℚ) : ℝ)
      = ((251259/5000000 : ℚ) : ℝ) * ((79533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c397 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-64003/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5663333/10000000) (δ := 7749/500000000) (ψ := 56493/500000) 307 292
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t397 : ((-16063614259/500000000000 : ℚ) : ℝ) ≤ stT307 397 := by
  have hc : ((-64013/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16063614259/500000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-64013/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c398 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-497303/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7594209/10000000) (δ := 3081/200000000) (ψ := 56493/500000) 307 292
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t398 : ((-49860135603/1000000000000 : ℚ) : ℝ) ≤ stT307 398 := by
  have hc : ((-497353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).2
  have h0 : (0:ℝ) ≤ ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49860135603/1000000000000 : ℚ) : ℝ)
      = ((100251/2000000 : ℚ) : ℝ) * ((-497353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c399 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-157201/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -618779/1000000) (δ := 7749/500000000) (ψ := 56493/500000) 307 293
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t399 : ((-78709077567/2000000000000 : ℚ) : ℝ) ≤ stT307 399 := by
  have hc : ((-157221/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).2
  have h0 : (0:ℝ) ≤ ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78709077567/2000000000000 : ℚ) : ℝ)
      = ((500627/10000000 : ℚ) : ℝ) * ((-157221/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c400 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-2709/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -213333/500000) (δ := 3101/200000000) (ψ := 56493/500000) 307 293
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t400 : ((-1355502711/200000000000 : ℚ) : ℝ) ≤ stT307 400 := by
  have hc : ((-2711/20000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1355502711/200000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-2711/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c401 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((294847/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -235029/1000000) (δ := 7749/500000000) (ψ := 56493/500000) 307 293
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t401 : ((9200909167/312500000000 : ℚ) : ℝ) ≤ stT307 401 := by
  have hc : ((294797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).1
  have hw2 : ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31211/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9200909167/312500000000 : ℚ) : ℝ)
      = ((31211/625000 : ℚ) : ℝ) * ((294797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c402 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((984639/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -219377/5000000) (δ := 3081/200000000) (ψ := 56493/500000) 307 293
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t402 : ((245521382203/5000000000000 : ℚ) : ℝ) ≤ stT307 402 := by
  have hc : ((984539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).1
  have hw2 : ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((249377/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((245521382203/5000000000000 : ℚ) : ℝ)
      = ((249377/5000000 : ℚ) : ℝ) * ((984539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c403 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((832473/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14681/100000) (δ := 3101/200000000) (ψ := 56493/500000) 307 293
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t403 : ((82926824871/2000000000000 : ℚ) : ℝ) ≤ stT307 403 := by
  have hc : ((832373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).1
  have hw2 : ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((99627/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82926824871/2000000000000 : ℚ) : ℝ)
      = ((99627/2000000 : ℚ) : ℝ) * ((832373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c404 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((110441/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 674039/2000000) (δ := 3081/200000000) (ψ := 56493/500000) 307 293
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t404 : ((27460754769/2500000000000 : ℚ) : ℝ) ≤ stT307 404 := by
  have hc : ((110391/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).1
  have hw2 : ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((248759/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27460754769/2500000000000 : ℚ) : ℝ)
      = ((248759/5000000 : ℚ) : ℝ) * ((110391/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c405 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-510913/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 658451/1250000) (δ := 7749/500000000) (ψ := 56493/500000) 307 293
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t405 : ((-31740550469/1250000000000 : ℚ) : ℝ) ≤ stT307 405 := by
  have hc : ((-511013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).2
  have h0 : (0:ℝ) ≤ ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31740550469/1250000000000 : ℚ) : ℝ)
      = ((62113/1250000 : ℚ) : ℝ) * ((-511013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c406 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-192351/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 358017/500000) (δ := 7699/500000000) (ψ := 56493/500000) 307 293
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t406 : ((-23868047083/500000000000 : ℚ) : ℝ) ≤ stT307 406 := by
  have hc : ((-192371/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).2
  have h0 : (0:ℝ) ≤ ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23868047083/500000000000 : ℚ) : ℝ)
      = ((124073/2500000 : ℚ) : ℝ) * ((-192371/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c407 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-35521/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6659573/10000000) (δ := 3853/250000000) (ψ := 56493/500000) 307 294
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t407 : ((-352182061/8000000000 : ℚ) : ℝ) ≤ stT307 407 := by
  have hc : ((-1421/1600 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).2
  have h0 : (0:ℝ) ≤ ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-352182061/8000000000 : ℚ) : ℝ)
      = ((247841/5000000 : ℚ) : ℝ) * ((-1421/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c408 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-166581/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74627/156250) (δ := 3853/250000000) (ψ := 56493/500000) 307 294
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t408 : ((-41247337847/2500000000000 : ℚ) : ℝ) ≤ stT307 408 := by
  have hc : ((-166631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).2
  have h0 : (0:ℝ) ≤ ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41247337847/2500000000000 : ℚ) : ℝ)
      = ((247537/5000000 : ℚ) : ℝ) * ((-166631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c409 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((200167/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -362161/1250000) (δ := 3853/250000000) (ψ := 56493/500000) 307 294
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t409 : ((24737863189/1250000000000 : ℚ) : ℝ) ≤ stT307 409 := by
  have hc : ((200117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24737863189/1250000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((200117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c410 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((917431/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1023053/10000000) (δ := 3853/250000000) (ψ := 56493/500000) 307 294
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t410 : ((56629594623/1250000000000 : ℚ) : ℝ) ≤ stT307 410 := by
  have hc : ((917331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).1
  have hw2 : ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61733/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56629594623/1250000000000 : ℚ) : ℝ)
      = ((61733/1250000 : ℚ) : ℝ) * ((917331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c411 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((1179/1250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 423327/5000000) (δ := 1939/125000000) (ψ := 56493/500000) 307 294
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t411 : ((4651963353/100000000000 : ℚ) : ℝ) ≤ stT307 411 := by
  have hc : ((9431/10000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).1
  have hw2 : ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((493263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4651963353/100000000000 : ℚ) : ℝ)
      = ((493263/10000000 : ℚ) : ℝ) * ((9431/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c412 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((58397/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 542351/2000000) (δ := 15491/1000000000) (ψ := 56493/500000) 307 294
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t412 : ((7190985327/312500000000 : ℚ) : ℝ) ≤ stT307 412 := by
  have hc : ((116769/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).1
  have hw2 : ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61583/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7190985327/312500000000 : ℚ) : ℝ)
      = ((61583/1250000 : ℚ) : ℝ) * ((116769/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c413 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-127639/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4572329/10000000) (δ := 3853/250000000) (ψ := 56493/500000) 307 294
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t413 : ((-15707917713/1250000000000 : ℚ) : ℝ) ≤ stT307 413 := by
  have hc : ((-127689/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15707917713/1250000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-127689/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c414 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-420893/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6428451/10000000) (δ := 3853/250000000) (ψ := 56493/500000) 307 294
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t414 : ((-103441269991/2500000000000 : ℚ) : ℝ) ≤ stT307 414 := by
  have hc : ((-420943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103441269991/2500000000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-420943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c415 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-246377/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3713921/5000000) (δ := 1923/125000000) (ψ := 56493/500000) 307 295
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t415 : ((-60477030081/1250000000000 : ℚ) : ℝ) ≤ stT307 415 := by
  have hc : ((-123201/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60477030081/1250000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-123201/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c416 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-38393/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55807/100000) (δ := 3871/250000000) (ψ := 56493/500000) 307 295
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t416 : ((-75307226727/2500000000000 : ℚ) : ℝ) ≤ stT307 416 := by
  have hc : ((-153597/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75307226727/2500000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-153597/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c417 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((75551/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -934483/2500000) (δ := 15419/1000000000) (ψ := 56493/500000) 307 295
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t417 : ((18474252801/5000000000000 : ℚ) : ℝ) ≤ stT307 417 := by
  have hc : ((75451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).1
  have hw2 : ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((244851/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18474252801/5000000000000 : ℚ) : ℝ)
      = ((244851/5000000 : ℚ) : ℝ) * ((75451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c418 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((362471/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -59363/312500) (δ := 15419/1000000000) (ψ := 56493/500000) 307 295
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t418 : ((35453109483/1000000000000 : ℚ) : ℝ) ≤ stT307 418 := by
  have hc : ((362421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).1
  have hw2 : ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((97823/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35453109483/1000000000000 : ℚ) : ℝ)
      = ((97823/2000000 : ℚ) : ℝ) * ((362421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c419 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((199931/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2627/400000) (δ := 1923/125000000) (ψ := 56493/500000) 307 295
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t419 : ((97662720741/2000000000000 : ℚ) : ℝ) ≤ stT307 419 := by
  have hc : ((199911/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97662720741/2000000000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((199911/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c420 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((761251/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 440973/2500000) (δ := 15519/1000000000) (ψ := 56493/500000) 307 295
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t420 : ((7428072609/200000000000 : ℚ) : ℝ) ≤ stT307 420 := by
  have hc : ((761151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7428072609/200000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((761151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c421 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((4211/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3589083/10000000) (δ := 3871/250000000) (ψ := 56493/500000) 307 295
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t421 : ((1640633631/250000000000 : ℚ) : ℝ) ≤ stT307 421 := by
  have hc : ((33663/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1640633631/250000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((33663/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c422 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-559013/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5409977/10000000) (δ := 1923/125000000) (ψ := 56493/500000) 307 295
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t422 : ((-272172294609/10000000000000 : ℚ) : ℝ) ≤ stT307 422 := by
  have hc : ((-559113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).2
  have h0 : (0:ℝ) ≤ ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-272172294609/10000000000000 : ℚ) : ℝ)
      = ((486793/10000000 : ℚ) : ℝ) * ((-559113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c423 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-484333/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56457/78125) (δ := 1923/125000000) (ψ := 56493/500000) 307 295
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t423 : ((-235515249111/5000000000000 : ℚ) : ℝ) ≤ stT307 423 := by
  have hc : ((-484383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).2
  have h0 : (0:ℝ) ≤ ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-235515249111/5000000000000 : ℚ) : ℝ)
      = ((486217/10000000 : ℚ) : ℝ) * ((-484383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c424 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-111223/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6669169/10000000) (δ := 15527/1000000000) (ψ := 56493/500000) 307 296
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t424 : ((-108041483853/2500000000000 : ℚ) : ℝ) ≤ stT307 424 := by
  have hc : ((-222471/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).2
  have h0 : (0:ℝ) ≤ ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108041483853/2500000000000 : ℚ) : ℝ)
      = ((485643/10000000 : ℚ) : ℝ) * ((-222471/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c425 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-91259/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -486117/1000000) (δ := 3869/250000000) (ψ := 56493/500000) 307 296
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t425 : ((-691864257/39062500000 : ℚ) : ℝ) ≤ stT307 425 := by
  have hc : ((-22821/62500 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-691864257/39062500000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-22821/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c426 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((85217/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3057391/10000000) (δ := 15427/1000000000) (ψ := 56493/500000) 307 296
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t426 : ((5159451149/312500000000 : ℚ) : ℝ) ≤ stT307 426 := by
  have hc : ((10649/31250 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).1
  have hw2 : ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((484501/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5159451149/312500000000 : ℚ) : ℝ)
      = ((484501/10000000 : ℚ) : ℝ) * ((10649/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c427 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((219019/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -628917/5000000) (δ := 961/62500000) (ψ := 56493/500000) 307 296
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t427 : ((52989211701/1250000000000 : ℚ) : ℝ) ≤ stT307 427 := by
  have hc : ((109497/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).1
  have hw2 : ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((483933/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52989211701/1250000000000 : ℚ) : ℝ)
      = ((483933/10000000 : ℚ) : ℝ) * ((109497/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c428 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((976983/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21497/400000) (δ := 3869/250000000) (ψ := 56493/500000) 307 296
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t428 : ((59024247743/1250000000000 : ℚ) : ℝ) ≤ stT307 428 := by
  have hc : ((976883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).1
  have hw2 : ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59024247743/1250000000000 : ℚ) : ℝ)
      = ((60421/1250000 : ℚ) : ℝ) * ((976883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c429 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((298337/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2328617/10000000) (δ := 15427/1000000000) (ψ := 56493/500000) 307 296
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t429 : ((36003539187/1250000000000 : ℚ) : ℝ) ≤ stT307 429 := by
  have hc : ((298287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).1
  have hw2 : ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((120701/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36003539187/1250000000000 : ℚ) : ℝ)
      = ((120701/2500000 : ℚ) : ℝ) * ((298287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c430 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-75367/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4115587/10000000) (δ := 961/62500000) (ψ := 56493/500000) 307 296
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t430 : ((-36393432481/10000000000000 : ℚ) : ℝ) ≤ stT307 430 := by
  have hc : ((-75467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36393432481/10000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-75467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c431 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-177331/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 184323/312500) (δ := 961/62500000) (ψ := 56493/500000) 307 296
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t431 : ((-5339346719/156250000000 : ℚ) : ℝ) ≤ stT307 431 := by
  have hc : ((-44339/62500 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).2
  have h0 : (0:ℝ) ≤ ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5339346719/156250000000 : ℚ) : ℝ)
      = ((120421/2500000 : ℚ) : ℝ) * ((-44339/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c432 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-124687/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7677017/10000000) (δ := 3869/250000000) (ψ := 56493/500000) 307 296
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t432 : ((-59996171637/1250000000000 : ℚ) : ℝ) ≤ stT307 432 := by
  have hc : ((-249399/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).2
  have h0 : (0:ℝ) ≤ ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59996171637/1250000000000 : ℚ) : ℝ)
      = ((240563/5000000 : ℚ) : ℝ) * ((-249399/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c433 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-802657/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1564083/2500000) (δ := 7767/500000000) (ψ := 56493/500000) 307 297
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t433 : ((-38578093149/1000000000000 : ℚ) : ℝ) ≤ stT307 433 := by
  have hc : ((-802757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).2
  have h0 : (0:ℝ) ≤ ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38578093149/1000000000000 : ℚ) : ℝ)
      = ((48057/1000000 : ℚ) : ℝ) * ((-802757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c434 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-55423/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4485863/10000000) (δ := 7767/500000000) (ψ := 56493/500000) 307 297
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t434 : ((-207936931/19531250000 : ℚ) : ℝ) ≤ stT307 434 := by
  have hc : ((-6931/31250 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).2
  have h0 : (0:ℝ) ≤ ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207936931/19531250000 : ℚ) : ℝ)
      = ((30001/625000 : ℚ) : ℝ) * ((-6931/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c435 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((7257/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1359731/5000000) (δ := 7717/500000000) (ψ := 56493/500000) 307 297
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t435 : ((55659421281/2500000000000 : ℚ) : ℝ) ≤ stT307 435 := by
  have hc : ((116087/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55659421281/2500000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((116087/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c436 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((927603/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -957129/10000000) (δ := 15469/1000000000) (ψ := 56493/500000) 307 297
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t436 : ((444193244239/10000000000000 : ℚ) : ℝ) ≤ stT307 436 := by
  have hc : ((927503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((444193244239/10000000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((927503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c437 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((237273/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 801137/10000000) (δ := 15369/1000000000) (ψ := 56493/500000) 307 297
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t437 : ((443323837/9765625000 : ℚ) : ℝ) ≤ stT307 437 := by
  have hc : ((14828/15625 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).1
  have hw2 : ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((119591/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((443323837/9765625000 : ℚ) : ℝ)
      = ((119591/2500000 : ℚ) : ℝ) * ((14828/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c438 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((260747/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2555489/10000000) (δ := 7767/500000000) (ψ := 56493/500000) 307 297
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t438 : ((62282859573/2500000000000 : ℚ) : ℝ) ≤ stT307 438 := by
  have hc : ((260697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).1
  have hw2 : ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((238909/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62282859573/2500000000000 : ℚ) : ℝ)
      = ((238909/5000000 : ℚ) : ℝ) * ((260697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c439 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-150933/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1076443/2500000) (δ := 15469/1000000000) (ψ := 56493/500000) 307 297
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t439 : ((-36042062021/5000000000000 : ℚ) : ℝ) ≤ stT307 439 := by
  have hc : ((-151033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36042062021/5000000000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-151033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c440 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-7513/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1210413/2000000) (δ := 15369/1000000000) (ψ := 56493/500000) 307 297
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t440 : ((-447770531/12500000000 : ℚ) : ℝ) ≤ stT307 440 := by
  have hc : ((-3757/5000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-447770531/12500000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-3757/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c441 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-249929/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7794367/10000000) (δ := 7717/500000000) (ψ := 56493/500000) 307 297
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t441 : ((-59512922607/1250000000000 : ℚ) : ℝ) ≤ stT307 441 := by
  have hc : ((-124977/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59512922607/1250000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-124977/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c442 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-195721/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6175209/10000000) (δ := 7681/500000000) (ψ := 56493/500000) 307 298
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t442 : ((-11638372049/312500000000 : ℚ) : ℝ) ≤ stT307 442 := by
  have hc : ((-97873/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11638372049/312500000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-97873/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c443 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-40811/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -138773/312500) (δ := 7731/500000000) (ψ := 56493/500000) 307 298
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t443 : ((-3879884113/400000000000 : ℚ) : ℝ) ≤ stT307 443 := by
  have hc : ((-40831/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).2
  have h0 : (0:ℝ) ≤ ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3879884113/400000000000 : ℚ) : ℝ)
      = ((95023/2000000 : ℚ) : ℝ) * ((-40831/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c444 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((233867/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2710177/10000000) (δ := 7731/500000000) (ψ := 56493/500000) 307 298
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t444 : ((55482202113/2500000000000 : ℚ) : ℝ) ≤ stT307 444 := by
  have hc : ((233817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).1
  have hw2 : ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237289/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55482202113/2500000000000 : ℚ) : ℝ)
      = ((237289/5000000 : ℚ) : ℝ) * ((233817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c445 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((461803/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -245883/2500000) (δ := 7681/500000000) (ψ := 56493/500000) 307 298
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t445 : ((43778340177/1000000000000 : ℚ) : ℝ) ≤ stT307 445 := by
  have hc : ((461753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).1
  have hw2 : ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94809/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43778340177/1000000000000 : ℚ) : ℝ)
      = ((94809/2000000 : ℚ) : ℝ) * ((461753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c446 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((191319/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29571/400000) (δ := 7731/500000000) (ψ := 56493/500000) 307 298
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t446 : ((90582563387/2000000000000 : ℚ) : ℝ) ≤ stT307 446 := by
  have hc : ((191299/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90582563387/2000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((191299/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c447 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((277153/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 307271/1250000) (δ := 7731/500000000) (ψ := 56493/500000) 307 298
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t447 : ((131065008249/5000000000000 : ℚ) : ℝ) ≤ stT307 447 := by
  have hc : ((277103/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131065008249/5000000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((277103/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c448 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-19673/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4173301/10000000) (δ := 15541/1000000000) (ψ := 56493/500000) 307 298
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t448 : ((-1163009501/250000000000 : ℚ) : ℝ) ≤ stT307 448 := by
  have hc : ((-19693/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).2
  have h0 : (0:ℝ) ≤ ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1163009501/250000000000 : ℚ) : ℝ)
      = ((59057/1250000 : ℚ) : ℝ) * ((-19693/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c449 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-705417/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5884519/10000000) (δ := 15541/1000000000) (ψ := 56493/500000) 307 298
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t449 : ((-33295463781/1000000000000 : ℚ) : ℝ) ≤ stT307 449 := by
  have hc : ((-705517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).2
  have h0 : (0:ℝ) ≤ ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33295463781/1000000000000 : ℚ) : ℝ)
      = ((47193/1000000 : ℚ) : ℝ) * ((-705517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c450 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-994513/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 948997/1250000) (δ := 15441/1000000000) (ψ := 56493/500000) 307 298
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t450 : ((-93773108253/2000000000000 : ℚ) : ℝ) ≤ stT307 450 := by
  have hc : ((-994613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).2
  have h0 : (0:ℝ) ≤ ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93773108253/2000000000000 : ℚ) : ℝ)
      = ((94281/2000000 : ℚ) : ℝ) * ((-994613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c451 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-20957/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6412291/10000000) (δ := 3071/200000000) (ψ := 56493/500000) 307 299
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t451 : ((-9869451279/250000000000 : ℚ) : ℝ) ≤ stT307 451 := by
  have hc : ((-41919/50000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9869451279/250000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-41919/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c452 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-309033/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -294527/625000) (δ := 3071/200000000) (ψ := 56493/500000) 307 299
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t452 : ((-145404107013/10000000000000 : ℚ) : ℝ) ≤ stT307 452 := by
  have hc : ((-309133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145404107013/10000000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-309133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c453 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((356289/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3016257/10000000) (δ := 3071/200000000) (ψ := 56493/500000) 307 299
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t453 : ((2091897997/125000000000 : ℚ) : ℝ) ≤ stT307 453 := by
  have hc : ((356189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).1
  have hw2 : ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5873/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2091897997/125000000000 : ℚ) : ℝ)
      = ((5873/125000 : ℚ) : ℝ) * ((356189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c454 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((431513/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1323919/10000000) (δ := 3887/250000000) (ψ := 56493/500000) 307 299
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t454 : ((202495509549/5000000000000 : ℚ) : ℝ) ≤ stT307 454 := by
  have hc : ((431463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).1
  have hw2 : ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((469323/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202495509549/5000000000000 : ℚ) : ℝ)
      = ((469323/10000000 : ℚ) : ℝ) * ((431463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c455 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((247343/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 364811/10000000) (δ := 1931/125000000) (ψ := 56493/500000) 307 299
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t455 : ((57972204813/1250000000000 : ℚ) : ℝ) ≤ stT307 455 := by
  have hc : ((123659/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).1
  have hw2 : ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((468807/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57972204813/1250000000000 : ℚ) : ℝ)
      = ((468807/10000000 : ℚ) : ℝ) * ((123659/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c456 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((341143/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102489/500000) (δ := 3091/200000000) (ψ := 56493/500000) 307 299
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t456 : ((39932780789/1250000000000 : ℚ) : ℝ) ≤ stT307 456 := by
  have hc : ((341093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).1
  have hw2 : ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117073/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39932780789/1250000000000 : ℚ) : ℝ)
      = ((117073/2500000 : ℚ) : ℝ) * ((341093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c457 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((979/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3730989/10000000) (δ := 3071/200000000) (ψ := 56493/500000) 307 299
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t457 : ((91474379/25000000000 : ℚ) : ℝ) ≤ stT307 457 := by
  have hc : ((3911/50000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).1
  have hw2 : ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((23389/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91474379/25000000000 : ℚ) : ℝ)
      = ((23389/500000 : ℚ) : ℝ) * ((3911/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c458 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-558553/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5408591/10000000) (δ := 3887/250000000) (ψ := 56493/500000) 307 299
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t458 : ((-26104178731/1000000000000 : ℚ) : ℝ) ≤ stT307 458 := by
  have hc : ((-558653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).2
  have h0 : (0:ℝ) ≤ ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26104178731/1000000000000 : ℚ) : ℝ)
      = ((46727/1000000 : ℚ) : ℝ) * ((-558653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c459 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-238193/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1416517/2000000) (δ := 1931/125000000) (ψ := 56493/500000) 307 299
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t459 : ((-55595435949/1250000000000 : ℚ) : ℝ) ≤ stT307 459 := by
  have hc : ((-119109/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).2
  have h0 : (0:ℝ) ≤ ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55595435949/1250000000000 : ℚ) : ℝ)
      = ((466761/10000000 : ℚ) : ℝ) * ((-119109/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c460 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-936061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1391029/2000000) (δ := 3071/200000000) (ψ := 56493/500000) 307 300
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t460 : ((-436487874733/10000000000000 : ℚ) : ℝ) ≤ stT307 460 := by
  have hc : ((-936161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).2
  have h0 : (0:ℝ) ≤ ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-436487874733/10000000000000 : ℚ) : ℝ)
      = ((466253/10000000 : ℚ) : ℝ) * ((-936161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c461 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-518059/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2644221/5000000) (δ := 3071/200000000) (ψ := 56493/500000) 307 300
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t461 : ((-241330999773/10000000000000 : ℚ) : ℝ) ≤ stT307 461 := by
  have hc : ((-518159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).2
  have h0 : (0:ℝ) ≤ ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-241330999773/10000000000000 : ℚ) : ℝ)
      = ((465747/10000000 : ℚ) : ℝ) * ((-518159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c462 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((24067/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3625423/10000000) (δ := 3071/200000000) (ψ := 56493/500000) 307 300
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t462 : ((5593837187/1000000000000 : ℚ) : ℝ) ≤ stT307 462 := by
  have hc : ((24047/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5593837187/1000000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((24047/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c463 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((44151/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -393187/2000000) (δ := 3887/250000000) (ψ := 56493/500000) 307 300
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t463 : ((82063147881/2500000000000 : ℚ) : ℝ) ≤ stT307 463 := by
  have hc : ((176579/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82063147881/2500000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((176579/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c464 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((992319/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -310053/10000000) (δ := 3091/200000000) (ψ := 56493/500000) 307 300
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t464 : ((230312882061/5000000000000 : ℚ) : ℝ) ≤ stT307 464 := by
  have hc : ((992219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230312882061/5000000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((992219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c465 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((859289/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1342297/10000000) (δ := 3887/250000000) (ψ := 56493/500000) 307 300
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t465 : ((199219294241/5000000000000 : ℚ) : ℝ) ≤ stT307 465 := by
  have hc : ((859189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199219294241/5000000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((859189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c466 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((73139/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2991041/10000000) (δ := 3071/200000000) (ψ := 56493/500000) 307 300
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t466 : ((33871718679/2000000000000 : ℚ) : ℝ) ≤ stT307 466 := by
  have hc : ((73119/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33871718679/2000000000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((73119/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c467 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-55983/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2318127/5000000) (δ := 3071/200000000) (ψ := 56493/500000) 307 300
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t467 : ((-5183021647/400000000000 : ℚ) : ℝ) ≤ stT307 467 := by
  have hc : ((-56003/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5183021647/400000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-56003/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c468 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-807781/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 392371/625000) (δ := 3887/250000000) (ψ := 56493/500000) 307 300
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t468 : ((-373443800131/10000000000000 : ℚ) : ℝ) ≤ stT307 468 := by
  have hc : ((-807881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-373443800131/10000000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-807881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c469 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-999691/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3895899/5000000) (δ := 15363/1000000000) (ψ := 56493/500000) 307 301
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t469 : ((-230830746289/5000000000000 : ℚ) : ℝ) ≤ stT307 469 := by
  have hc : ((-999791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230830746289/5000000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-999791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c470 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-194589/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -61571/100000) (δ := 193/12500000) (ψ := 56493/500000) 307 301
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t470 : ((-22442205331/625000000000 : ℚ) : ℝ) ≤ stT307 470 := by
  have hc : ((-97307/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22442205331/625000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-97307/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c471 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-237261/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -905171/2000000) (δ := 15463/1000000000) (ψ := 56493/500000) 307 301
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t471 : ((-13671281517/1250000000000 : ℚ) : ℝ) ≤ stT307 471 := by
  have hc : ((-237361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13671281517/1250000000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-237361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c472 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((400049/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -579613/2000000) (δ := 777/50000000) (ψ := 56493/500000) 307 301
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t472 : ((184091325363/10000000000000 : ℚ) : ℝ) ≤ stT307 472 := by
  have hc : ((399949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184091325363/10000000000000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((399949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c473 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((872993/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9951/78125) (δ := 777/50000000) (ψ := 56493/500000) 307 301
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t473 : ((2006781007/50000000000 : ℚ) : ℝ) ≤ stT307 473 := by
  have hc : ((872893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2006781007/50000000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((872893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c474 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((99037/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10851/312500) (δ := 777/50000000) (ψ := 56493/500000) 307 301
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t474 : ((9096917301/200000000000 : ℚ) : ℝ) ≤ stT307 474 := by
  have hc : ((99027/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9096917301/200000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((99027/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c475 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((141351/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1964739/10000000) (δ := 15463/1000000000) (ψ := 56493/500000) 307 301
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t475 : ((64847044061/2000000000000 : ℚ) : ℝ) ≤ stT307 475 := by
  have hc : ((141331/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64847044061/2000000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((141331/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c476 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((13883/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3578791/10000000) (δ := 193/12500000) (ψ := 56493/500000) 307 301
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t476 : ((6358675677/1000000000000 : ℚ) : ℝ) ≤ stT307 476 := by
  have hc : ((13873/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6358675677/1000000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((13873/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c477 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-483799/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5189467/10000000) (δ := 15463/1000000000) (ψ := 56493/500000) 307 301
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t477 : ((-221562351231/10000000000000 : ℚ) : ℝ) ≤ stT307 477 := by
  have hc : ((-483899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).2
  have h0 : (0:ℝ) ≤ ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221562351231/10000000000000 : ℚ) : ℝ)
      = ((457869/10000000 : ℚ) : ℝ) * ((-483899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c478 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-911921/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3398421/5000000) (δ := 15363/1000000000) (ψ := 56493/500000) 307 301
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t478 : ((-41714928519/1000000000000 : ℚ) : ℝ) ≤ stT307 478 := by
  have hc : ((-912021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41714928519/1000000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-912021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c479 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-488089/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4567/6250) (δ := 15433/1000000000) (ψ := 56493/500000) 307 302
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t479 : ((-13939785423/312500000000 : ℚ) : ℝ) ≤ stT307 479 := by
  have hc : ((-488139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13939785423/312500000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-488139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c480 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-653201/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2853251/5000000) (δ := 15433/1000000000) (ψ := 56493/500000) 307 302
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t480 : ((-74547523809/2500000000000 : ℚ) : ℝ) ≤ stT307 480 := by
  have hc : ((-653301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74547523809/2500000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-653301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c481 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-36421/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2054629/5000000) (δ := 15533/1000000000) (ψ := 56493/500000) 307 302
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t481 : ((-16629353631/5000000000000 : ℚ) : ℝ) ≤ stT307 481 := by
  have hc : ((-36471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16629353631/5000000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-36471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c482 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((133791/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2515237/10000000) (δ := 15433/1000000000) (ψ := 56493/500000) 307 302
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t482 : ((30464337021/1250000000000 : ℚ) : ℝ) ≤ stT307 482 := by
  have hc : ((66883/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).1
  have hw2 : ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((455487/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30464337021/1250000000000 : ℚ) : ℝ)
      = ((455487/10000000 : ℚ) : ℝ) * ((66883/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c483 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((466193/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -924593/10000000) (δ := 1537/100000000) (ψ := 56493/500000) 307 302
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t483 : ((42420411429/1000000000000 : ℚ) : ℝ) ≤ stT307 483 := by
  have hc : ((466143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42420411429/1000000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((466143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c484 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((482529/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 662827/10000000) (δ := 15433/1000000000) (ψ := 56493/500000) 307 302
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t484 : ((43861683411/1000000000000 : ℚ) : ℝ) ≤ stT307 484 := by
  have hc : ((482479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43861683411/1000000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((482479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c485 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((62259/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 224687/1000000) (δ := 15533/1000000000) (ψ := 56493/500000) 307 302
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t485 : ((7066444231/250000000000 : ℚ) : ℝ) ≤ stT307 485 := by
  have hc : ((62249/100000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7066444231/250000000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((62249/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c486 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((39679/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3827767/10000000) (δ := 1537/100000000) (ψ := 56493/500000) 307 302
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t486 : ((17953390611/10000000000000 : ℚ) : ℝ) ≤ stT307 486 := by
  have hc : ((39579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17953390611/10000000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((39579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c487 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-557481/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5405363/10000000) (δ := 15433/1000000000) (ψ := 56493/500000) 307 302
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t487 : ((-31583060583/1250000000000 : ℚ) : ℝ) ≤ stT307 487 := by
  have hc : ((-557581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).2
  have h0 : (0:ℝ) ≤ ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31583060583/1250000000000 : ℚ) : ℝ)
      = ((56643/1250000 : ℚ) : ℝ) * ((-557581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c488 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-234869/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 872467/1250000) (δ := 1537/100000000) (ψ := 56493/500000) 307 302
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t488 : ((-53165790513/1250000000000 : ℚ) : ℝ) ≤ stT307 488 := by
  have hc : ((-117447/125000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53165790513/1250000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-117447/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c489 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-192281/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1431431/2000000) (δ := 7713/500000000) (ψ := 56493/500000) 307 303
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t489 : ((-10870198627/250000000000 : ℚ) : ℝ) ≤ stT307 489 := by
  have hc : ((-192301/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10870198627/250000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-192301/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c490 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-616977/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5589229/10000000) (δ := 15377/1000000000) (ψ := 56493/500000) 307 303
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t490 : ((-139383501529/5000000000000 : ℚ) : ℝ) ≤ stT307 490 := by
  have hc : ((-617077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139383501529/5000000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-617077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c491 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-19487/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -80489/200000) (δ := 15377/1000000000) (ψ := 56493/500000) 307 303
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t491 : ((-4408465439/2500000000000 : ℚ) : ℝ) ≤ stT307 491 := by
  have hc : ((-19537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4408465439/2500000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-19537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c492 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((552731/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -492579/2000000) (δ := 7763/500000000) (ψ := 56493/500000) 307 303
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t492 : ((124572422127/5000000000000 : ℚ) : ℝ) ≤ stT307 492 := by
  have hc : ((552631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124572422127/5000000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((552631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c493 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((233813/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -904563/10000000) (δ := 7763/500000000) (ψ := 56493/500000) 307 303
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t493 : ((26323184519/625000000000 : ℚ) : ℝ) ≤ stT307 493 := by
  have hc : ((58447/62500 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26323184519/625000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((58447/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c494 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((483159/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 650699/10000000) (δ := 7763/500000000) (ψ := 56493/500000) 307 303
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t494 : ((217360884389/5000000000000 : ℚ) : ℝ) ≤ stT307 494 := by
  have hc : ((483109/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).1
  have hw2 : ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449921/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217360884389/5000000000000 : ℚ) : ℝ)
      = ((449921/10000000 : ℚ) : ℝ) * ((483109/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c495 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((636307/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1101369/5000000) (δ := 15377/1000000000) (ψ := 56493/500000) 307 303
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t495 : ((142976707731/5000000000000 : ℚ) : ℝ) ≤ stT307 495 := by
  have hc : ((636207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142976707731/5000000000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((636207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c496 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((8757/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1875853/5000000) (δ := 7763/500000000) (ψ := 56493/500000) 307 303
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t496 : ((7852788357/2500000000000 : ℚ) : ℝ) ≤ stT307 496 := by
  have hc : ((17489/250000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7852788357/2500000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((17489/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c497 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-104233/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 662191/1250000) (δ := 7713/500000000) (ψ := 56493/500000) 307 303
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t497 : ((-23381967093/1000000000000 : ℚ) : ℝ) ≤ stT307 497 := by
  have hc : ((-104253/200000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23381967093/1000000000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-104253/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c498 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-918901/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6840203/10000000) (δ := 7713/500000000) (ψ := 56493/500000) 307 303
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t498 : ((-411814457111/10000000000000 : ℚ) : ℝ) ≤ stT307 498 := by
  have hc : ((-919001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-411814457111/10000000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-919001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c499 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-488981/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1465631/2000000) (δ := 1923/125000000) (ψ := 56493/500000) 307 304
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t499 : ((-109460297761/2500000000000 : ℚ) : ℝ) ≤ stT307 499 := by
  have hc : ((-489031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109460297761/2500000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-489031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_c500 :
    |Real.cos (((307 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-339299/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -289581/500000) (δ := 1923/125000000) (ψ := 56493/500000) 307 304
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st307_t500 : ((-75880811843/2500000000000 : ℚ) : ℝ) ≤ stT307 500 := by
  have hc : ((-339349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((307 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((56493/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st307_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).2
  have h0 : (0:ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75880811843/2500000000000 : ℚ) : ℝ)
      = ((223607/5000000 : ℚ) : ℝ) * ((-339349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st307_p1 : ((248381/250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT307 (i+1) := by
  rw [Finset.sum_range_one]
  exact st307_t1

theorem st307_p2 : ((14075724495051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT307 (i+1))
      = (∑ i ∈ Finset.range 1, stT307 (i+1)) + stT307 2 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 1
    simpa using h
  have hprev := st307_p1
  have hstep := st307_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p3 : ((11007188479593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT307 (i+1))
      = (∑ i ∈ Finset.range 2, stT307 (i+1)) + stT307 3 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 2
    simpa using h
  have hprev := st307_p2
  have hstep := st307_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p4 : ((9981878274531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT307 (i+1))
      = (∑ i ∈ Finset.range 3, stT307 (i+1)) + stT307 4 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 3
    simpa using h
  have hprev := st307_p3
  have hstep := st307_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p5 : ((6722719721811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT307 (i+1))
      = (∑ i ∈ Finset.range 4, stT307 (i+1)) + stT307 5 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 4
    simpa using h
  have hprev := st307_p4
  have hstep := st307_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p6 : ((2704658303551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT307 (i+1))
      = (∑ i ∈ Finset.range 5, stT307 (i+1)) + stT307 6 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 5
    simpa using h
  have hprev := st307_p5
  have hstep := st307_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p7 : ((6215943799907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT307 (i+1))
      = (∑ i ∈ Finset.range 6, stT307 (i+1)) + stT307 7 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 6
    simpa using h
  have hprev := st307_p6
  have hstep := st307_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p8 : ((3169154948999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT307 (i+1))
      = (∑ i ∈ Finset.range 7, stT307 (i+1)) + stT307 8 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 7
    simpa using h
  have hprev := st307_p7
  have hstep := st307_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p9 : ((1388814592931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT307 (i+1))
      = (∑ i ∈ Finset.range 8, stT307 (i+1)) + stT307 9 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 8
    simpa using h
  have hprev := st307_p8
  have hstep := st307_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p10 : ((-1764232717587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT307 (i+1))
      = (∑ i ∈ Finset.range 9, stT307 (i+1)) + stT307 10 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 9
    simpa using h
  have hprev := st307_p9
  have hstep := st307_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p11 : ((90321077131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT307 (i+1))
      = (∑ i ∈ Finset.range 10, stT307 (i+1)) + stT307 11 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 10
    simpa using h
  have hprev := st307_p10
  have hstep := st307_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p12 : ((-2201656087797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT307 (i+1))
      = (∑ i ∈ Finset.range 11, stT307 (i+1)) + stT307 12 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 11
    simpa using h
  have hprev := st307_p11
  have hstep := st307_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p13 : ((-634497366167/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT307 (i+1))
      = (∑ i ∈ Finset.range 12, stT307 (i+1)) + stT307 13 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 12
    simpa using h
  have hprev := st307_p12
  have hstep := st307_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p14 : ((-770038487467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT307 (i+1))
      = (∑ i ∈ Finset.range 13, stT307 (i+1)) + stT307 14 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 13
    simpa using h
  have hprev := st307_p13
  have hstep := st307_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p15 : ((-1551028192231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT307 (i+1))
      = (∑ i ∈ Finset.range 14, stT307 (i+1)) + stT307 15 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 14
    simpa using h
  have hprev := st307_p14
  have hstep := st307_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p16 : ((-123116613991/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT307 (i+1))
      = (∑ i ∈ Finset.range 15, stT307 (i+1)) + stT307 16 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 15
    simpa using h
  have hprev := st307_p15
  have hstep := st307_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p17 : ((-6023144840353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT307 (i+1))
      = (∑ i ∈ Finset.range 16, stT307 (i+1)) + stT307 17 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 16
    simpa using h
  have hprev := st307_p16
  have hstep := st307_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p18 : ((-1079490427451/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT307 (i+1))
      = (∑ i ∈ Finset.range 17, stT307 (i+1)) + stT307 18 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 17
    simpa using h
  have hprev := st307_p17
  have hstep := st307_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p19 : ((-63455959249/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT307 (i+1))
      = (∑ i ∈ Finset.range 18, stT307 (i+1)) + stT307 19 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 18
    simpa using h
  have hprev := st307_p18
  have hstep := st307_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p20 : ((-135851948761/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT307 (i+1))
      = (∑ i ∈ Finset.range 19, stT307 (i+1)) + stT307 20 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 19
    simpa using h
  have hprev := st307_p19
  have hstep := st307_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p21 : ((-1116691802777/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT307 (i+1))
      = (∑ i ∈ Finset.range 20, stT307 (i+1)) + stT307 21 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 20
    simpa using h
  have hprev := st307_p20
  have hstep := st307_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p22 : ((-3457830978829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT307 (i+1))
      = (∑ i ∈ Finset.range 21, stT307 (i+1)) + stT307 22 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 21
    simpa using h
  have hprev := st307_p21
  have hstep := st307_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p23 : ((-2618477113069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT307 (i+1))
      = (∑ i ∈ Finset.range 22, stT307 (i+1)) + stT307 23 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 22
    simpa using h
  have hprev := st307_p22
  have hstep := st307_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p24 : ((-2792031672877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT307 (i+1))
      = (∑ i ∈ Finset.range 23, stT307 (i+1)) + stT307 24 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 23
    simpa using h
  have hprev := st307_p23
  have hstep := st307_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p25 : ((-578841544793/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT307 (i+1))
      = (∑ i ∈ Finset.range 24, stT307 (i+1)) + stT307 25 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 24
    simpa using h
  have hprev := st307_p24
  have hstep := st307_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p26 : ((-999089379079/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT307 (i+1))
      = (∑ i ∈ Finset.range 25, stT307 (i+1)) + stT307 26 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 25
    simpa using h
  have hprev := st307_p25
  have hstep := st307_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p27 : ((-43412508829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT307 (i+1))
      = (∑ i ∈ Finset.range 26, stT307 (i+1)) + stT307 27 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 26
    simpa using h
  have hprev := st307_p26
  have hstep := st307_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p28 : ((13907879859/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT307 (i+1))
      = (∑ i ∈ Finset.range 27, stT307 (i+1)) + stT307 28 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 27
    simpa using h
  have hprev := st307_p27
  have hstep := st307_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p29 : ((-704210027881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT307 (i+1))
      = (∑ i ∈ Finset.range 28, stT307 (i+1)) + stT307 29 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 28
    simpa using h
  have hprev := st307_p28
  have hstep := st307_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p30 : ((-246792529223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT307 (i+1))
      = (∑ i ∈ Finset.range 29, stT307 (i+1)) + stT307 30 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 29
    simpa using h
  have hprev := st307_p29
  have hstep := st307_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p31 : ((-284526285299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT307 (i+1))
      = (∑ i ∈ Finset.range 30, stT307 (i+1)) + stT307 31 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 30
    simpa using h
  have hprev := st307_p30
  have hstep := st307_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p32 : ((-32368883729/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT307 (i+1))
      = (∑ i ∈ Finset.range 31, stT307 (i+1)) + stT307 32 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 31
    simpa using h
  have hprev := st307_p31
  have hstep := st307_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p33 : ((-32712107389/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT307 (i+1))
      = (∑ i ∈ Finset.range 32, stT307 (i+1)) + stT307 33 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 32
    simpa using h
  have hprev := st307_p32
  have hstep := st307_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p34 : ((-151080048041/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT307 (i+1))
      = (∑ i ∈ Finset.range 33, stT307 (i+1)) + stT307 34 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 33
    simpa using h
  have hprev := st307_p33
  have hstep := st307_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p35 : ((-142943630859/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT307 (i+1))
      = (∑ i ∈ Finset.range 34, stT307 (i+1)) + stT307 35 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 34
    simpa using h
  have hprev := st307_p34
  have hstep := st307_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p36 : ((8557592303/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT307 (i+1))
      = (∑ i ∈ Finset.range 35, stT307 (i+1)) + stT307 36 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 35
    simpa using h
  have hprev := st307_p35
  have hstep := st307_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p37 : ((-106505860723/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT307 (i+1))
      = (∑ i ∈ Finset.range 36, stT307 (i+1)) + stT307 37 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 36
    simpa using h
  have hprev := st307_p36
  have hstep := st307_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p38 : ((-280749255429/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT307 (i+1))
      = (∑ i ∈ Finset.range 37, stT307 (i+1)) + stT307 38 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 37
    simpa using h
  have hprev := st307_p37
  have hstep := st307_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p39 : ((47733160323/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT307 (i+1))
      = (∑ i ∈ Finset.range 38, stT307 (i+1)) + stT307 39 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 38
    simpa using h
  have hprev := st307_p38
  have hstep := st307_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p40 : ((115015325637/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT307 (i+1))
      = (∑ i ∈ Finset.range 39, stT307 (i+1)) + stT307 40 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 39
    simpa using h
  have hprev := st307_p39
  have hstep := st307_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p41 : ((-23751813571/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT307 (i+1))
      = (∑ i ∈ Finset.range 40, stT307 (i+1)) + stT307 41 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 40
    simpa using h
  have hprev := st307_p40
  have hstep := st307_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p42 : ((-1079711948653/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT307 (i+1))
      = (∑ i ∈ Finset.range 41, stT307 (i+1)) + stT307 42 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 41
    simpa using h
  have hprev := st307_p41
  have hstep := st307_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p43 : ((-2098349773041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT307 (i+1))
      = (∑ i ∈ Finset.range 42, stT307 (i+1)) + stT307 43 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 42
    simpa using h
  have hprev := st307_p42
  have hstep := st307_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p44 : ((-1001670623061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT307 (i+1))
      = (∑ i ∈ Finset.range 43, stT307 (i+1)) + stT307 44 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 43
    simpa using h
  have hprev := st307_p43
  have hstep := st307_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p45 : ((237144895797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT307 (i+1))
      = (∑ i ∈ Finset.range 44, stT307 (i+1)) + stT307 45 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 44
    simpa using h
  have hprev := st307_p44
  have hstep := st307_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p46 : ((935863213383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT307 (i+1))
      = (∑ i ∈ Finset.range 45, stT307 (i+1)) + stT307 46 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 45
    simpa using h
  have hprev := st307_p45
  have hstep := st307_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p47 : ((379812105571/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT307 (i+1))
      = (∑ i ∈ Finset.range 46, stT307 (i+1)) + stT307 47 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 46
    simpa using h
  have hprev := st307_p46
  have hstep := st307_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p48 : ((2009564353159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT307 (i+1))
      = (∑ i ∈ Finset.range 47, stT307 (i+1)) + stT307 48 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 47
    simpa using h
  have hprev := st307_p47
  have hstep := st307_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p49 : ((4939487001639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT307 (i+1))
      = (∑ i ∈ Finset.range 48, stT307 (i+1)) + stT307 49 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 48
    simpa using h
  have hprev := st307_p48
  have hstep := st307_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p50 : ((1483759449833/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT307 (i+1))
      = (∑ i ∈ Finset.range 49, stT307 (i+1)) + stT307 50 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 49
    simpa using h
  have hprev := st307_p49
  have hstep := st307_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p51 : ((1775405917463/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT307 (i+1))
      = (∑ i ∈ Finset.range 50, stT307 (i+1)) + stT307 51 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 50
    simpa using h
  have hprev := st307_p50
  have hstep := st307_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p52 : ((4220080266301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT307 (i+1))
      = (∑ i ∈ Finset.range 51, stT307 (i+1)) + stT307 52 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 51
    simpa using h
  have hprev := st307_p51
  have hstep := st307_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p53 : ((9793522715717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT307 (i+1))
      = (∑ i ∈ Finset.range 52, stT307 (i+1)) + stT307 53 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 52
    simpa using h
  have hprev := st307_p52
  have hstep := st307_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p54 : ((10820029903319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT307 (i+1))
      = (∑ i ∈ Finset.range 53, stT307 (i+1)) + stT307 54 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 53
    simpa using h
  have hprev := st307_p53
  have hstep := st307_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p55 : ((34668991149/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT307 (i+1))
      = (∑ i ∈ Finset.range 54, stT307 (i+1)) + stT307 55 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 54
    simpa using h
  have hprev := st307_p54
  have hstep := st307_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p56 : ((2599798045613/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT307 (i+1))
      = (∑ i ∈ Finset.range 55, stT307 (i+1)) + stT307 56 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 55
    simpa using h
  have hprev := st307_p55
  have hstep := st307_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p57 : ((2273668881287/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT307 (i+1))
      = (∑ i ∈ Finset.range 56, stT307 (i+1)) + stT307 57 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 56
    simpa using h
  have hprev := st307_p56
  have hstep := st307_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p58 : ((4075599465349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT307 (i+1))
      = (∑ i ∈ Finset.range 57, stT307 (i+1)) + stT307 58 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 57
    simpa using h
  have hprev := st307_p57
  have hstep := st307_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p59 : ((8452509422747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT307 (i+1))
      = (∑ i ∈ Finset.range 58, stT307 (i+1)) + stT307 59 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 58
    simpa using h
  have hprev := st307_p58
  have hstep := st307_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p60 : ((1942800067373/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT307 (i+1))
      = (∑ i ∈ Finset.range 59, stT307 (i+1)) + stT307 60 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 59
    simpa using h
  have hprev := st307_p59
  have hstep := st307_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p61 : ((10411078769313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT307 (i+1))
      = (∑ i ∈ Finset.range 60, stT307 (i+1)) + stT307 61 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 60
    simpa using h
  have hprev := st307_p60
  have hstep := st307_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p62 : ((9577954917309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT307 (i+1))
      = (∑ i ∈ Finset.range 61, stT307 (i+1)) + stT307 62 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 61
    simpa using h
  have hprev := st307_p61
  have hstep := st307_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p63 : ((8481761826277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT307 (i+1))
      = (∑ i ∈ Finset.range 62, stT307 (i+1)) + stT307 63 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 62
    simpa using h
  have hprev := st307_p62
  have hstep := st307_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p64 : ((8960689326277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT307 (i+1))
      = (∑ i ∈ Finset.range 63, stT307 (i+1)) + stT307 64 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 63
    simpa using h
  have hprev := st307_p63
  have hstep := st307_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p65 : ((10127446538767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT307 (i+1))
      = (∑ i ∈ Finset.range 64, stT307 (i+1)) + stT307 65 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 64
    simpa using h
  have hprev := st307_p64
  have hstep := st307_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p66 : ((605054026387/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT307 (i+1))
      = (∑ i ∈ Finset.range 65, stT307 (i+1)) + stT307 66 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 65
    simpa using h
  have hprev := st307_p65
  have hstep := st307_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p67 : ((4294909964441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT307 (i+1))
      = (∑ i ∈ Finset.range 66, stT307 (i+1)) + stT307 67 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 66
    simpa using h
  have hprev := st307_p66
  have hstep := st307_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p68 : ((4652597829287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT307 (i+1))
      = (∑ i ∈ Finset.range 67, stT307 (i+1)) + stT307 68 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 67
    simpa using h
  have hprev := st307_p67
  have hstep := st307_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p69 : ((2522256599629/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT307 (i+1))
      = (∑ i ∈ Finset.range 68, stT307 (i+1)) + stT307 69 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 68
    simpa using h
  have hprev := st307_p68
  have hstep := st307_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p70 : ((8994702216383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT307 (i+1))
      = (∑ i ∈ Finset.range 69, stT307 (i+1)) + stT307 70 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 69
    simpa using h
  have hprev := st307_p69
  have hstep := st307_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p71 : ((8927698878227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT307 (i+1))
      = (∑ i ∈ Finset.range 70, stT307 (i+1)) + stT307 71 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 70
    simpa using h
  have hprev := st307_p70
  have hstep := st307_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p72 : ((5014813348957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT307 (i+1))
      = (∑ i ∈ Finset.range 71, stT307 (i+1)) + stT307 72 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 71
    simpa using h
  have hprev := st307_p71
  have hstep := st307_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p73 : ((4578964794689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT307 (i+1))
      = (∑ i ∈ Finset.range 72, stT307 (i+1)) + stT307 73 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 72
    simpa using h
  have hprev := st307_p72
  have hstep := st307_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p74 : ((8932252116983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT307 (i+1))
      = (∑ i ∈ Finset.range 73, stT307 (i+1)) + stT307 74 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 73
    simpa using h
  have hprev := st307_p73
  have hstep := st307_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p75 : ((9997376264483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT307 (i+1))
      = (∑ i ∈ Finset.range 74, stT307 (i+1)) + stT307 75 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 74
    simpa using h
  have hprev := st307_p74
  have hstep := st307_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p76 : ((35182270853/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT307 (i+1))
      = (∑ i ∈ Finset.range 75, stT307 (i+1)) + stT307 76 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 75
    simpa using h
  have hprev := st307_p75
  have hstep := st307_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p77 : ((9200240341693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT307 (i+1))
      = (∑ i ∈ Finset.range 76, stT307 (i+1)) + stT307 77 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 76
    simpa using h
  have hprev := st307_p76
  have hstep := st307_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p78 : ((1976885102521/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT307 (i+1))
      = (∑ i ∈ Finset.range 77, stT307 (i+1)) + stT307 78 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 77
    simpa using h
  have hprev := st307_p77
  have hstep := st307_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p79 : ((350891716037/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT307 (i+1))
      = (∑ i ∈ Finset.range 78, stT307 (i+1)) + stT307 79 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 78
    simpa using h
  have hprev := st307_p78
  have hstep := st307_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p80 : ((9714935592083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT307 (i+1))
      = (∑ i ∈ Finset.range 79, stT307 (i+1)) + stT307 80 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 79
    simpa using h
  have hprev := st307_p79
  have hstep := st307_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p81 : ((9353576414107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT307 (i+1))
      = (∑ i ∈ Finset.range 80, stT307 (i+1)) + stT307 81 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 80
    simpa using h
  have hprev := st307_p80
  have hstep := st307_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p82 : ((9033257410831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT307 (i+1))
      = (∑ i ∈ Finset.range 81, stT307 (i+1)) + stT307 82 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 81
    simpa using h
  have hprev := st307_p81
  have hstep := st307_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p83 : ((9874835996861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT307 (i+1))
      = (∑ i ∈ Finset.range 82, stT307 (i+1)) + stT307 83 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 82
    simpa using h
  have hprev := st307_p82
  have hstep := st307_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p84 : ((8797896343071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT307 (i+1))
      = (∑ i ∈ Finset.range 83, stT307 (i+1)) + stT307 84 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 83
    simpa using h
  have hprev := st307_p83
  have hstep := st307_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p85 : ((9824007505327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT307 (i+1))
      = (∑ i ∈ Finset.range 84, stT307 (i+1)) + stT307 85 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 84
    simpa using h
  have hprev := st307_p84
  have hstep := st307_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p86 : ((9056404031839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT307 (i+1))
      = (∑ i ∈ Finset.range 85, stT307 (i+1)) + stT307 86 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 85
    simpa using h
  have hprev := st307_p85
  have hstep := st307_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p87 : ((9458319522623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT307 (i+1))
      = (∑ i ∈ Finset.range 86, stT307 (i+1)) + stT307 87 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 86
    simpa using h
  have hprev := st307_p86
  have hstep := st307_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p88 : ((9439709224791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT307 (i+1))
      = (∑ i ∈ Finset.range 87, stT307 (i+1)) + stT307 88 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 87
    simpa using h
  have hprev := st307_p87
  have hstep := st307_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p89 : ((9116246595099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT307 (i+1))
      = (∑ i ∈ Finset.range 88, stT307 (i+1)) + stT307 89 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 88
    simpa using h
  have hprev := st307_p88
  have hstep := st307_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p90 : ((9710112541071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT307 (i+1))
      = (∑ i ∈ Finset.range 89, stT307 (i+1)) + stT307 90 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 89
    simpa using h
  have hprev := st307_p89
  have hstep := st307_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p91 : ((4461462467153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT307 (i+1))
      = (∑ i ∈ Finset.range 90, stT307 (i+1)) + stT307 91 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 90
    simpa using h
  have hprev := st307_p90
  have hstep := st307_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p92 : ((4916904832493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT307 (i+1))
      = (∑ i ∈ Finset.range 91, stT307 (i+1)) + stT307 92 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 91
    simpa using h
  have hprev := st307_p91
  have hstep := st307_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p93 : ((4426436906013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT307 (i+1))
      = (∑ i ∈ Finset.range 92, stT307 (i+1)) + stT307 93 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 92
    simpa using h
  have hprev := st307_p92
  have hstep := st307_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p94 : ((9865895292807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT307 (i+1))
      = (∑ i ∈ Finset.range 93, stT307 (i+1)) + stT307 94 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 93
    simpa using h
  have hprev := st307_p93
  have hstep := st307_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p95 : ((4421610485583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT307 (i+1))
      = (∑ i ∈ Finset.range 94, stT307 (i+1)) + stT307 95 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 94
    simpa using h
  have hprev := st307_p94
  have hstep := st307_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p96 : ((4931851083423/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT307 (i+1))
      = (∑ i ∈ Finset.range 95, stT307 (i+1)) + stT307 96 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 95
    simpa using h
  have hprev := st307_p95
  have hstep := st307_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p97 : ((884875318287/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT307 (i+1))
      = (∑ i ∈ Finset.range 96, stT307 (i+1)) + stT307 97 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 96
    simpa using h
  have hprev := st307_p96
  have hstep := st307_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p98 : ((4929027317443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT307 (i+1))
      = (∑ i ∈ Finset.range 97, stT307 (i+1)) + stT307 98 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 97
    simpa using h
  have hprev := st307_p97
  have hstep := st307_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p99 : ((4426505302329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT307 (i+1))
      = (∑ i ∈ Finset.range 98, stT307 (i+1)) + stT307 99 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 98
    simpa using h
  have hprev := st307_p98
  have hstep := st307_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p100 : ((9852008605659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT307 (i+1))
      = (∑ i ∈ Finset.range 99, stT307 (i+1)) + stT307 100 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 99
    simpa using h
  have hprev := st307_p99
  have hstep := st307_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p101 : ((8865172703893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT307 (i+1))
      = (∑ i ∈ Finset.range 100, stT307 (i+1)) + stT307 101 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 100
    simpa using h
  have hprev := st307_p100
  have hstep := st307_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p102 : ((1228170350801/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT307 (i+1))
      = (∑ i ∈ Finset.range 101, stT307 (i+1)) + stT307 102 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 101
    simpa using h
  have hprev := st307_p101
  have hstep := st307_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p103 : ((4457463377189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT307 (i+1))
      = (∑ i ∈ Finset.range 102, stT307 (i+1)) + stT307 103 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 102
    simpa using h
  have hprev := st307_p102
  have hstep := st307_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p104 : ((4870702342529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT307 (i+1))
      = (∑ i ∈ Finset.range 103, stT307 (i+1)) + stT307 104 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 103
    simpa using h
  have hprev := st307_p103
  have hstep := st307_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p105 : ((9041932522813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT307 (i+1))
      = (∑ i ∈ Finset.range 104, stT307 (i+1)) + stT307 105 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 104
    simpa using h
  have hprev := st307_p104
  have hstep := st307_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p106 : ((9563802010743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT307 (i+1))
      = (∑ i ∈ Finset.range 105, stT307 (i+1)) + stT307 106 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 105
    simpa using h
  have hprev := st307_p105
  have hstep := st307_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p107 : ((9270244586797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT307 (i+1))
      = (∑ i ∈ Finset.range 106, stT307 (i+1)) + stT307 107 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 106
    simpa using h
  have hprev := st307_p106
  have hstep := st307_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p108 : ((9291959682547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT307 (i+1))
      = (∑ i ∈ Finset.range 107, stT307 (i+1)) + stT307 108 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 107
    simpa using h
  have hprev := st307_p107
  have hstep := st307_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p109 : ((9565231271651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT307 (i+1))
      = (∑ i ∈ Finset.range 108, stT307 (i+1)) + stT307 109 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 108
    simpa using h
  have hprev := st307_p108
  have hstep := st307_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p110 : ((9005456958203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT307 (i+1))
      = (∑ i ∈ Finset.range 109, stT307 (i+1)) + stT307 110 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 109
    simpa using h
  have hprev := st307_p109
  have hstep := st307_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p111 : ((9799202787651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT307 (i+1))
      = (∑ i ∈ Finset.range 110, stT307 (i+1)) + stT307 111 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 110
    simpa using h
  have hprev := st307_p110
  have hstep := st307_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p112 : ((8871549605331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT307 (i+1))
      = (∑ i ∈ Finset.range 111, stT307 (i+1)) + stT307 112 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 111
    simpa using h
  have hprev := st307_p111
  have hstep := st307_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p113 : ((9789353666131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT307 (i+1))
      = (∑ i ∈ Finset.range 112, stT307 (i+1)) + stT307 113 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 112
    simpa using h
  have hprev := st307_p112
  have hstep := st307_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p114 : ((9047908168989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT307 (i+1))
      = (∑ i ∈ Finset.range 113, stT307 (i+1)) + stT307 114 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 113
    simpa using h
  have hprev := st307_p113
  have hstep := st307_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p115 : ((9455929956709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT307 (i+1))
      = (∑ i ∈ Finset.range 114, stT307 (i+1)) + stT307 115 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 114
    simpa using h
  have hprev := st307_p114
  have hstep := st307_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p116 : ((9484241975377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT307 (i+1))
      = (∑ i ∈ Finset.range 115, stT307 (i+1)) + stT307 116 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 115
    simpa using h
  have hprev := st307_p115
  have hstep := st307_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p117 : ((70400316041/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT307 (i+1))
      = (∑ i ∈ Finset.range 116, stT307 (i+1)) + stT307 117 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 116
    simpa using h
  have hprev := st307_p116
  have hstep := st307_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p118 : ((2454199944709/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT307 (i+1))
      = (∑ i ∈ Finset.range 117, stT307 (i+1)) + stT307 118 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 117
    simpa using h
  have hprev := st307_p117
  have hstep := st307_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p119 : ((1780194511917/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT307 (i+1))
      = (∑ i ∈ Finset.range 118, stT307 (i+1)) + stT307 119 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 118
    simpa using h
  have hprev := st307_p118
  have hstep := st307_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p120 : ((1928940836049/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT307 (i+1))
      = (∑ i ∈ Finset.range 119, stT307 (i+1)) + stT307 120 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 119
    simpa using h
  have hprev := st307_p119
  have hstep := st307_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p121 : ((4662797074167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT307 (i+1))
      = (∑ i ∈ Finset.range 120, stT307 (i+1)) + stT307 121 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 120
    simpa using h
  have hprev := st307_p120
  have hstep := st307_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p122 : ((909601527741/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT307 (i+1))
      = (∑ i ∈ Finset.range 121, stT307 (i+1)) + stT307 122 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 121
    simpa using h
  have hprev := st307_p121
  have hstep := st307_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p123 : ((1224696207861/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT307 (i+1))
      = (∑ i ∈ Finset.range 122, stT307 (i+1)) + stT307 123 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 122
    simpa using h
  have hprev := st307_p122
  have hstep := st307_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p124 : ((2224924280883/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT307 (i+1))
      = (∑ i ∈ Finset.range 123, stT307 (i+1)) + stT307 124 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 123
    simpa using h
  have hprev := st307_p123
  have hstep := st307_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p125 : ((9610347102269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT307 (i+1))
      = (∑ i ∈ Finset.range 124, stT307 (i+1)) + stT307 125 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 124
    simpa using h
  have hprev := st307_p124
  have hstep := st307_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p126 : ((235329956021/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT307 (i+1))
      = (∑ i ∈ Finset.range 125, stT307 (i+1)) + stT307 126 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 125
    simpa using h
  have hprev := st307_p125
  have hstep := st307_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p127 : ((899417939187/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT307 (i+1))
      = (∑ i ∈ Finset.range 126, stT307 (i+1)) + stT307 127 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 126
    simpa using h
  have hprev := st307_p126
  have hstep := st307_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p128 : ((1228222147111/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT307 (i+1))
      = (∑ i ∈ Finset.range 127, stT307 (i+1)) + stT307 128 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 127
    simpa using h
  have hprev := st307_p127
  have hstep := st307_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p129 : ((1803437189231/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT307 (i+1))
      = (∑ i ∈ Finset.range 128, stT307 (i+1)) + stT307 129 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 128
    simpa using h
  have hprev := st307_p128
  have hstep := st307_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p130 : ((9352801837493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT307 (i+1))
      = (∑ i ∈ Finset.range 129, stT307 (i+1)) + stT307 130 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 129
    simpa using h
  have hprev := st307_p129
  have hstep := st307_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p131 : ((9689970327021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT307 (i+1))
      = (∑ i ∈ Finset.range 130, stT307 (i+1)) + stT307 131 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 130
    simpa using h
  have hprev := st307_p130
  have hstep := st307_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p132 : ((8877617124763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT307 (i+1))
      = (∑ i ∈ Finset.range 131, stT307 (i+1)) + stT307 132 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 131
    simpa using h
  have hprev := st307_p131
  have hstep := st307_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p133 : ((38622498421/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT307 (i+1))
      = (∑ i ∈ Finset.range 132, stT307 (i+1)) + stT307 133 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 132
    simpa using h
  have hprev := st307_p132
  have hstep := st307_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p134 : ((1884732564143/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT307 (i+1))
      = (∑ i ∈ Finset.range 133, stT307 (i+1)) + stT307 134 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 133
    simpa using h
  have hprev := st307_p133
  have hstep := st307_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p135 : ((8946659287551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT307 (i+1))
      = (∑ i ∈ Finset.range 134, stT307 (i+1)) + stT307 135 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 134
    simpa using h
  have hprev := st307_p134
  have hstep := st307_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p136 : ((9799108377099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT307 (i+1))
      = (∑ i ∈ Finset.range 135, stT307 (i+1)) + stT307 136 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 135
    simpa using h
  have hprev := st307_p135
  have hstep := st307_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p137 : ((1838920107867/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT307 (i+1))
      = (∑ i ∈ Finset.range 136, stT307 (i+1)) + stT307 137 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 136
    simpa using h
  have hprev := st307_p136
  have hstep := st307_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p138 : ((9090093419959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT307 (i+1))
      = (∑ i ∈ Finset.range 137, stT307 (i+1)) + stT307 138 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 137
    simpa using h
  have hprev := st307_p137
  have hstep := st307_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p139 : ((9824875291607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT307 (i+1))
      = (∑ i ∈ Finset.range 138, stT307 (i+1)) + stT307 139 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 138
    simpa using h
  have hprev := st307_p138
  have hstep := st307_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p140 : ((9052403621607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT307 (i+1))
      = (∑ i ∈ Finset.range 139, stT307 (i+1)) + stT307 140 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 139
    simpa using h
  have hprev := st307_p139
  have hstep := st307_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p141 : ((460826226747/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT307 (i+1))
      = (∑ i ∈ Finset.range 140, stT307 (i+1)) + stT307 141 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 140
    simpa using h
  have hprev := st307_p140
  have hstep := st307_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p142 : ((612753875427/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT307 (i+1))
      = (∑ i ∈ Finset.range 141, stT307 (i+1)) + stT307 142 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 141
    simpa using h
  have hprev := st307_p141
  have hstep := st307_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p143 : ((8983119745003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT307 (i+1))
      = (∑ i ∈ Finset.range 142, stT307 (i+1)) + stT307 143 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 142
    simpa using h
  have hprev := st307_p142
  have hstep := st307_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p144 : ((9289386289163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT307 (i+1))
      = (∑ i ∈ Finset.range 143, stT307 (i+1)) + stT307 144 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 143
    simpa using h
  have hprev := st307_p143
  have hstep := st307_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p145 : ((9785613280961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT307 (i+1))
      = (∑ i ∈ Finset.range 144, stT307 (i+1)) + stT307 145 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 144
    simpa using h
  have hprev := st307_p144
  have hstep := st307_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p146 : ((8962172621959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT307 (i+1))
      = (∑ i ∈ Finset.range 145, stT307 (i+1)) + stT307 146 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 145
    simpa using h
  have hprev := st307_p145
  have hstep := st307_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p147 : ((9300955121031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT307 (i+1))
      = (∑ i ∈ Finset.range 146, stT307 (i+1)) + stT307 147 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 146
    simpa using h
  have hprev := st307_p146
  have hstep := st307_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p148 : ((9789675763701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT307 (i+1))
      = (∑ i ∈ Finset.range 147, stT307 (i+1)) + stT307 148 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 147
    simpa using h
  have hprev := st307_p147
  have hstep := st307_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p149 : ((8978407517973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT307 (i+1))
      = (∑ i ∈ Finset.range 148, stT307 (i+1)) + stT307 149 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 148
    simpa using h
  have hprev := st307_p148
  have hstep := st307_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p150 : ((9252488078757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT307 (i+1))
      = (∑ i ∈ Finset.range 149, stT307 (i+1)) + stT307 150 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 149
    simpa using h
  have hprev := st307_p149
  have hstep := st307_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p151 : ((1962522207013/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT307 (i+1))
      = (∑ i ∈ Finset.range 150, stT307 (i+1)) + stT307 151 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 150
    simpa using h
  have hprev := st307_p150
  have hstep := st307_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p152 : ((9038529304157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT307 (i+1))
      = (∑ i ∈ Finset.range 151, stT307 (i+1)) + stT307 152 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 151
    simpa using h
  have hprev := st307_p151
  have hstep := st307_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p153 : ((9150201587369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT307 (i+1))
      = (∑ i ∈ Finset.range 152, stT307 (i+1)) + stT307 153 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 152
    simpa using h
  have hprev := st307_p152
  have hstep := st307_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p154 : ((9829458766583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT307 (i+1))
      = (∑ i ∈ Finset.range 153, stT307 (i+1)) + stT307 154 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 153
    simpa using h
  have hprev := st307_p153
  have hstep := st307_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p155 : ((9160453615703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT307 (i+1))
      = (∑ i ∈ Finset.range 154, stT307 (i+1)) + stT307 155 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 154
    simpa using h
  have hprev := st307_p154
  have hstep := st307_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p156 : ((8803273443/9765625000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT307 (i+1))
      = (∑ i ∈ Finset.range 155, stT307 (i+1)) + stT307 156 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 155
    simpa using h
  have hprev := st307_p155
  have hstep := st307_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p157 : ((1224425317547/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT307 (i+1))
      = (∑ i ∈ Finset.range 156, stT307 (i+1)) + stT307 157 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 156
    simpa using h
  have hprev := st307_p156
  have hstep := st307_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p158 : ((4677634414007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT307 (i+1))
      = (∑ i ∈ Finset.range 157, stT307 (i+1)) + stT307 158 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 157
    simpa using h
  have hprev := st307_p157
  have hstep := st307_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p159 : ((889534069977/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT307 (i+1))
      = (∑ i ∈ Finset.range 158, stT307 (i+1)) + stT307 159 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 158
    simpa using h
  have hprev := st307_p158
  have hstep := st307_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p160 : ((1931664558903/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT307 (i+1))
      = (∑ i ∈ Finset.range 159, stT307 (i+1)) + stT307 160 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 159
    simpa using h
  have hprev := st307_p159
  have hstep := st307_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p161 : ((1919461448179/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT307 (i+1))
      = (∑ i ∈ Finset.range 160, stT307 (i+1)) + stT307 161 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 160
    simpa using h
  have hprev := st307_p160
  have hstep := st307_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p162 : ((221897570323/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT307 (i+1))
      = (∑ i ∈ Finset.range 161, stT307 (i+1)) + stT307 162 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 161
    simpa using h
  have hprev := st307_p161
  have hstep := st307_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p163 : ((234895378393/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT307 (i+1))
      = (∑ i ∈ Finset.range 162, stT307 (i+1)) + stT307 163 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 162
    simpa using h
  have hprev := st307_p162
  have hstep := st307_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p164 : ((306119309131/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT307 (i+1))
      = (∑ i ∈ Finset.range 163, stT307 (i+1)) + stT307 164 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 163
    simpa using h
  have hprev := st307_p163
  have hstep := st307_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p165 : ((9040012916541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT307 (i+1))
      = (∑ i ∈ Finset.range 164, stT307 (i+1)) + stT307 165 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 164
    simpa using h
  have hprev := st307_p164
  have hstep := st307_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p166 : ((9072309294191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT307 (i+1))
      = (∑ i ∈ Finset.range 165, stT307 (i+1)) + stT307 166 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 165
    simpa using h
  have hprev := st307_p165
  have hstep := st307_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p167 : ((1226003559481/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT307 (i+1))
      = (∑ i ∈ Finset.range 166, stT307 (i+1)) + stT307 167 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 166
    simpa using h
  have hprev := st307_p166
  have hstep := st307_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p168 : ((117339921587/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT307 (i+1))
      = (∑ i ∈ Finset.range 167, stT307 (i+1)) + stT307 168 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 167
    simpa using h
  have hprev := st307_p167
  have hstep := st307_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p169 : ((4433426785429/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT307 (i+1))
      = (∑ i ∈ Finset.range 168, stT307 (i+1)) + stT307 169 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 168
    simpa using h
  have hprev := st307_p168
  have hstep := st307_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p170 : ((4769488168273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT307 (i+1))
      = (∑ i ∈ Finset.range 169, stT307 (i+1)) + stT307 170 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 169
    simpa using h
  have hprev := st307_p169
  have hstep := st307_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p171 : ((152262172551/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT307 (i+1))
      = (∑ i ∈ Finset.range 170, stT307 (i+1)) + stT307 171 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 170
    simpa using h
  have hprev := st307_p170
  have hstep := st307_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p172 : ((1122911566753/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT307 (i+1))
      = (∑ i ∈ Finset.range 171, stT307 (i+1)) + stT307 172 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 171
    simpa using h
  have hprev := st307_p171
  have hstep := st307_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p173 : ((9101053837959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT307 (i+1))
      = (∑ i ∈ Finset.range 172, stT307 (i+1)) + stT307 173 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 172
    simpa using h
  have hprev := st307_p172
  have hstep := st307_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p174 : ((1962399173613/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT307 (i+1))
      = (∑ i ∈ Finset.range 173, stT307 (i+1)) + stT307 174 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 173
    simpa using h
  have hprev := st307_p173
  have hstep := st307_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p175 : ((1177681494197/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT307 (i+1))
      = (∑ i ∈ Finset.range 174, stT307 (i+1)) + stT307 175 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 174
    simpa using h
  have hprev := st307_p174
  have hstep := st307_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p176 : ((4427663117813/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT307 (i+1))
      = (∑ i ∈ Finset.range 175, stT307 (i+1)) + stT307 176 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 175
    simpa using h
  have hprev := st307_p175
  have hstep := st307_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p177 : ((117991084723/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT307 (i+1))
      = (∑ i ∈ Finset.range 176, stT307 (i+1)) + stT307 177 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 176
    simpa using h
  have hprev := st307_p176
  have hstep := st307_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p178 : ((1962602835481/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT307 (i+1))
      = (∑ i ∈ Finset.range 177, stT307 (i+1)) + stT307 178 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 177
    simpa using h
  have hprev := st307_p177
  have hstep := st307_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p179 : ((9116900122909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT307 (i+1))
      = (∑ i ∈ Finset.range 178, stT307 (i+1)) + stT307 179 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 178
    simpa using h
  have hprev := st307_p178
  have hstep := st307_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p180 : ((357774336313/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT307 (i+1))
      = (∑ i ∈ Finset.range 179, stT307 (i+1)) + stT307 180 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 179
    simpa using h
  have hprev := st307_p179
  have hstep := st307_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p181 : ((9683603685407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT307 (i+1))
      = (∑ i ∈ Finset.range 180, stT307 (i+1)) + stT307 181 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 180
    simpa using h
  have hprev := st307_p180
  have hstep := st307_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p182 : ((9670787472907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT307 (i+1))
      = (∑ i ∈ Finset.range 181, stT307 (i+1)) + stT307 182 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 181
    simpa using h
  have hprev := st307_p181
  have hstep := st307_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p183 : ((8937596045983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT307 (i+1))
      = (∑ i ∈ Finset.range 182, stT307 (i+1)) + stT307 183 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 182
    simpa using h
  have hprev := st307_p182
  have hstep := st307_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p184 : ((364247475911/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT307 (i+1))
      = (∑ i ∈ Finset.range 183, stT307 (i+1)) + stT307 184 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 183
    simpa using h
  have hprev := st307_p183
  have hstep := st307_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p185 : ((9803071986313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT307 (i+1))
      = (∑ i ∈ Finset.range 184, stT307 (i+1)) + stT307 185 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 184
    simpa using h
  have hprev := st307_p184
  have hstep := st307_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p186 : ((9511944298693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT307 (i+1))
      = (∑ i ∈ Finset.range 185, stT307 (i+1)) + stT307 186 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 185
    simpa using h
  have hprev := st307_p185
  have hstep := st307_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p187 : ((8864429845567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT307 (i+1))
      = (∑ i ∈ Finset.range 186, stT307 (i+1)) + stT307 187 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 186
    simpa using h
  have hprev := st307_p186
  have hstep := st307_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p188 : ((9245596447687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT307 (i+1))
      = (∑ i ∈ Finset.range 187, stT307 (i+1)) + stT307 188 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 187
    simpa using h
  have hprev := st307_p187
  have hstep := st307_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p189 : ((9842594702983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT307 (i+1))
      = (∑ i ∈ Finset.range 188, stT307 (i+1)) + stT307 189 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 188
    simpa using h
  have hprev := st307_p188
  have hstep := st307_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p190 : ((4699673921931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT307 (i+1))
      = (∑ i ∈ Finset.range 189, stT307 (i+1)) + stT307 190 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 189
    simpa using h
  have hprev := st307_p189
  have hstep := st307_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p191 : ((8844891857887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT307 (i+1))
      = (∑ i ∈ Finset.range 190, stT307 (i+1)) + stT307 191 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 190
    simpa using h
  have hprev := st307_p190
  have hstep := st307_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p192 : ((9326229662781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT307 (i+1))
      = (∑ i ∈ Finset.range 191, stT307 (i+1)) + stT307 192 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 191
    simpa using h
  have hprev := st307_p191
  have hstep := st307_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p193 : ((9850740138091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT307 (i+1))
      = (∑ i ∈ Finset.range 192, stT307 (i+1)) + stT307 193 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 192
    simpa using h
  have hprev := st307_p192
  have hstep := st307_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p194 : ((9350848261079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT307 (i+1))
      = (∑ i ∈ Finset.range 193, stT307 (i+1)) + stT307 194 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 193
    simpa using h
  have hprev := st307_p193
  have hstep := st307_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p195 : ((8840503177409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT307 (i+1))
      = (∑ i ∈ Finset.range 194, stT307 (i+1)) + stT307 195 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 194
    simpa using h
  have hprev := st307_p194
  have hstep := st307_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p196 : ((4670674552567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT307 (i+1))
      = (∑ i ∈ Finset.range 195, stT307 (i+1)) + stT307 196 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 195
    simpa using h
  have hprev := st307_p195
  have hstep := st307_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p197 : ((4926692097427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT307 (i+1))
      = (∑ i ∈ Finset.range 196, stT307 (i+1)) + stT307 197 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 196
    simpa using h
  have hprev := st307_p196
  have hstep := st307_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p198 : ((4683824888947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT307 (i+1))
      = (∑ i ∈ Finset.range 197, stT307 (i+1)) + stT307 198 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 197
    simpa using h
  have hprev := st307_p197
  have hstep := st307_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p199 : ((2209622126177/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT307 (i+1))
      = (∑ i ∈ Finset.range 198, stT307 (i+1)) + stT307 199 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 198
    simpa using h
  have hprev := st307_p198
  have hstep := st307_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p200 : ((4645956224521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT307 (i+1))
      = (∑ i ∈ Finset.range 199, stT307 (i+1)) + stT307 200 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 199
    simpa using h
  have hprev := st307_p199
  have hstep := st307_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p201 : ((4925254505551/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT307 (i+1))
      = (∑ i ∈ Finset.range 200, stT307 (i+1)) + stT307 201 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 200
    simpa using h
  have hprev := st307_p200
  have hstep := st307_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p202 : ((236193024191/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT307 (i+1))
      = (∑ i ∈ Finset.range 201, stT307 (i+1)) + stT307 202 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 201
    simpa using h
  have hprev := st307_p201
  have hstep := st307_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p203 : ((8851008976711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT307 (i+1))
      = (∑ i ∈ Finset.range 202, stT307 (i+1)) + stT307 203 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 202
    simpa using h
  have hprev := st307_p202
  have hstep := st307_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p204 : ((9181958853451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT307 (i+1))
      = (∑ i ∈ Finset.range 203, stT307 (i+1)) + stT307 204 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 203
    simpa using h
  have hprev := st307_p203
  have hstep := st307_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p205 : ((9818792216461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT307 (i+1))
      = (∑ i ∈ Finset.range 204, stT307 (i+1)) + stT307 205 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 204
    simpa using h
  have hprev := st307_p204
  have hstep := st307_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p206 : ((9582423813493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT307 (i+1))
      = (∑ i ∈ Finset.range 205, stT307 (i+1)) + stT307 206 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 205
    simpa using h
  have hprev := st307_p205
  have hstep := st307_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p207 : ((8911006479493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT307 (i+1))
      = (∑ i ∈ Finset.range 206, stT307 (i+1)) + stT307 207 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 206
    simpa using h
  have hprev := st307_p206
  have hstep := st307_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p208 : ((9028672216993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT307 (i+1))
      = (∑ i ∈ Finset.range 207, stT307 (i+1)) + stT307 208 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 207
    simpa using h
  have hprev := st307_p207
  have hstep := st307_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p209 : ((9718511672053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT307 (i+1))
      = (∑ i ∈ Finset.range 208, stT307 (i+1)) + stT307 209 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 208
    simpa using h
  have hprev := st307_p208
  have hstep := st307_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p210 : ((2435324922137/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT307 (i+1))
      = (∑ i ∈ Finset.range 209, stT307 (i+1)) + stT307 210 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 209
    simpa using h
  have hprev := st307_p209
  have hstep := st307_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p211 : ((9060075098033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT307 (i+1))
      = (∑ i ∈ Finset.range 210, stT307 (i+1)) + stT307 211 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 210
    simpa using h
  have hprev := st307_p210
  have hstep := st307_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p212 : ((1110035561937/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT307 (i+1))
      = (∑ i ∈ Finset.range 211, stT307 (i+1)) + stT307 212 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 211
    simpa using h
  have hprev := st307_p211
  have hstep := st307_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p213 : ((2378432973513/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT307 (i+1))
      = (∑ i ∈ Finset.range 212, stT307 (i+1)) + stT307 213 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 212
    simpa using h
  have hprev := st307_p212
  have hstep := st307_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p214 : ((9855507304427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT307 (i+1))
      = (∑ i ∈ Finset.range 213, stT307 (i+1)) + stT307 214 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 213
    simpa using h
  have hprev := st307_p213
  have hstep := st307_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p215 : ((291188409091/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT307 (i+1))
      = (∑ i ∈ Finset.range 214, stT307 (i+1)) + stT307 215 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 214
    simpa using h
  have hprev := st307_p214
  have hstep := st307_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p216 : ((2206351998521/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT307 (i+1))
      = (∑ i ∈ Finset.range 215, stT307 (i+1)) + stT307 216 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 215
    simpa using h
  have hprev := st307_p215
  have hstep := st307_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p217 : ((1151678299939/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT307 (i+1))
      = (∑ i ∈ Finset.range 216, stT307 (i+1)) + stT307 217 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 216
    simpa using h
  have hprev := st307_p216
  have hstep := st307_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p218 : ((9823436003177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT307 (i+1))
      = (∑ i ∈ Finset.range 217, stT307 (i+1)) + stT307 218 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 217
    simpa using h
  have hprev := st307_p217
  have hstep := st307_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p219 : ((9634346265851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT307 (i+1))
      = (∑ i ∈ Finset.range 218, stT307 (i+1)) + stT307 219 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 218
    simpa using h
  have hprev := st307_p218
  have hstep := st307_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p220 : ((8964253492251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT307 (i+1))
      = (∑ i ∈ Finset.range 219, stT307 (i+1)) + stT307 220 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 219
    simpa using h
  have hprev := st307_p219
  have hstep := st307_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p221 : ((8919052557343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT307 (i+1))
      = (∑ i ∈ Finset.range 220, stT307 (i+1)) + stT307 221 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 220
    simpa using h
  have hprev := st307_p220
  have hstep := st307_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p222 : ((9568949691043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT307 (i+1))
      = (∑ i ∈ Finset.range 221, stT307 (i+1)) + stT307 222 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 221
    simpa using h
  have hprev := st307_p221
  have hstep := st307_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p223 : ((9855914377013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT307 (i+1))
      = (∑ i ∈ Finset.range 222, stT307 (i+1)) + stT307 223 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 222
    simpa using h
  have hprev := st307_p222
  have hstep := st307_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p224 : ((9319988721767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT307 (i+1))
      = (∑ i ∈ Finset.range 223, stT307 (i+1)) + stT307 224 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 223
    simpa using h
  have hprev := st307_p223
  have hstep := st307_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p225 : ((4410978569709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT307 (i+1))
      = (∑ i ∈ Finset.range 224, stT307 (i+1)) + stT307 225 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 224
    simpa using h
  have hprev := st307_p224
  have hstep := st307_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p226 : ((2287806381057/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT307 (i+1))
      = (∑ i ∈ Finset.range 225, stT307 (i+1)) + stT307 226 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 225
    simpa using h
  have hprev := st307_p225
  have hstep := st307_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p227 : ((9784731207207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT307 (i+1))
      = (∑ i ∈ Finset.range 226, stT307 (i+1)) + stT307 227 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 226
    simpa using h
  have hprev := st307_p226
  have hstep := st307_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p228 : ((1946186257039/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT307 (i+1))
      = (∑ i ∈ Finset.range 227, stT307 (i+1)) + stT307 228 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 227
    simpa using h
  have hprev := st307_p227
  have hstep := st307_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p229 : ((4538538989137/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT307 (i+1))
      = (∑ i ∈ Finset.range 228, stT307 (i+1)) + stT307 229 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 228
    simpa using h
  have hprev := st307_p228
  have hstep := st307_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p230 : ((176659449891/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT307 (i+1))
      = (∑ i ∈ Finset.range 229, stT307 (i+1)) + stT307 230 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 229
    simpa using h
  have hprev := st307_p229
  have hstep := st307_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p231 : ((2342287809843/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT307 (i+1))
      = (∑ i ∈ Finset.range 230, stT307 (i+1)) + stT307 231 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 230
    simpa using h
  have hprev := st307_p230
  have hstep := st307_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p232 : ((2466947808141/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT307 (i+1))
      = (∑ i ∈ Finset.range 231, stT307 (i+1)) + stT307 232 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 231
    simpa using h
  have hprev := st307_p231
  have hstep := st307_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p233 : ((4789109395989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT307 (i+1))
      = (∑ i ∈ Finset.range 232, stT307 (i+1)) + stT307 233 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 232
    simpa using h
  have hprev := st307_p232
  have hstep := st307_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p234 : ((1787537584119/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT307 (i+1))
      = (∑ i ∈ Finset.range 233, stT307 (i+1)) + stT307 234 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 233
    simpa using h
  have hprev := st307_p233
  have hstep := st307_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p235 : ((2224642426863/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT307 (i+1))
      = (∑ i ∈ Finset.range 234, stT307 (i+1)) + stT307 235 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 234
    simpa using h
  have hprev := st307_p234
  have hstep := st307_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p236 : ((2378734378751/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT307 (i+1))
      = (∑ i ∈ Finset.range 235, stT307 (i+1)) + stT307 236 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 235
    simpa using h
  have hprev := st307_p235
  have hstep := st307_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p237 : ((617596004417/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT307 (i+1))
      = (∑ i ∈ Finset.range 236, stT307 (i+1)) + stT307 237 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 236
    simpa using h
  have hprev := st307_p236
  have hstep := st307_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p238 : ((2366863084001/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT307 (i+1))
      = (∑ i ∈ Finset.range 237, stT307 (i+1)) + stT307 238 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 237
    simpa using h
  have hprev := st307_p237
  have hstep := st307_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p239 : ((4436979285129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT307 (i+1))
      = (∑ i ∈ Finset.range 238, stT307 (i+1)) + stT307 239 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 238
    simpa using h
  have hprev := st307_p238
  have hstep := st307_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p240 : ((895136398851/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT307 (i+1))
      = (∑ i ∈ Finset.range 239, stT307 (i+1)) + stT307 240 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 239
    simpa using h
  have hprev := st307_p239
  have hstep := st307_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p241 : ((4792865374889/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT307 (i+1))
      = (∑ i ∈ Finset.range 240, stT307 (i+1)) + stT307 241 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 240
    simpa using h
  have hprev := st307_p240
  have hstep := st307_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p242 : ((197576565621/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT307 (i+1))
      = (∑ i ∈ Finset.range 241, stT307 (i+1)) + stT307 242 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 241
    simpa using h
  have hprev := st307_p241
  have hstep := st307_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p243 : ((1884396027279/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT307 (i+1))
      = (∑ i ∈ Finset.range 242, stT307 (i+1)) + stT307 243 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 242
    simpa using h
  have hprev := st307_p242
  have hstep := st307_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p244 : ((221369741757/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT307 (i+1))
      = (∑ i ∈ Finset.range 243, stT307 (i+1)) + stT307 244 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 243
    simpa using h
  have hprev := st307_p243
  have hstep := st307_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p245 : ((1120133496329/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT307 (i+1))
      = (∑ i ∈ Finset.range 244, stT307 (i+1)) + stT307 245 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 244
    simpa using h
  have hprev := st307_p244
  have hstep := st307_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p246 : ((299722737099/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT307 (i+1))
      = (∑ i ∈ Finset.range 245, stT307 (i+1)) + stT307 246 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 245
    simpa using h
  have hprev := st307_p245
  have hstep := st307_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p247 : ((2470996710607/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT307 (i+1))
      = (∑ i ∈ Finset.range 246, stT307 (i+1)) + stT307 247 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 246
    simpa using h
  have hprev := st307_p246
  have hstep := st307_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p248 : ((9445539606961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT307 (i+1))
      = (∑ i ∈ Finset.range 247, stT307 (i+1)) + stT307 248 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 247
    simpa using h
  have hprev := st307_p247
  have hstep := st307_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p249 : ((8868546936411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT307 (i+1))
      = (∑ i ∈ Finset.range 248, stT307 (i+1)) + stT307 249 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 248
    simpa using h
  have hprev := st307_p248
  have hstep := st307_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p250 : ((8922989927721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT307 (i+1))
      = (∑ i ∈ Finset.range 249, stT307 (i+1)) + stT307 250 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 249
    simpa using h
  have hprev := st307_p249
  have hstep := st307_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p251 : ((1906614855117/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT307 (i+1))
      = (∑ i ∈ Finset.range 250, stT307 (i+1)) + stT307 251 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 250
    simpa using h
  have hprev := st307_p250
  have hstep := st307_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p252 : ((1978683392793/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT307 (i+1))
      = (∑ i ∈ Finset.range 251, stT307 (i+1)) + stT307 252 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 251
    simpa using h
  have hprev := st307_p251
  have hstep := st307_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p253 : ((190697481831/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT307 (i+1))
      = (∑ i ∈ Finset.range 252, stT307 (i+1)) + stT307 253 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 252
    simpa using h
  have hprev := st307_p252
  have hstep := st307_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p254 : ((178527972711/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT307 (i+1))
      = (∑ i ∈ Finset.range 253, stT307 (i+1)) + stT307 254 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 253
    simpa using h
  have hprev := st307_p253
  have hstep := st307_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p255 : ((7082339927/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT307 (i+1))
      = (∑ i ∈ Finset.range 254, stT307 (i+1)) + stT307 255 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 254
    simpa using h
  have hprev := st307_p254
  have hstep := st307_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p256 : ((7524223927/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT307 (i+1))
      = (∑ i ∈ Finset.range 255, stT307 (i+1)) + stT307 256 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 255
    simpa using h
  have hprev := st307_p255
  have hstep := st307_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p257 : ((2469553020977/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT307 (i+1))
      = (∑ i ∈ Finset.range 256, stT307 (i+1)) + stT307 257 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 256
    simpa using h
  have hprev := st307_p256
  have hstep := st307_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p258 : ((9675478034761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT307 (i+1))
      = (∑ i ∈ Finset.range 257, stT307 (i+1)) + stT307 258 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 257
    simpa using h
  have hprev := st307_p257
  have hstep := st307_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p259 : ((9054872319861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT307 (i+1))
      = (∑ i ∈ Finset.range 258, stT307 (i+1)) + stT307 259 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 258
    simpa using h
  have hprev := st307_p258
  have hstep := st307_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p260 : ((8791031695041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT307 (i+1))
      = (∑ i ∈ Finset.range 259, stT307 (i+1)) + stT307 260 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 259
    simpa using h
  have hprev := st307_p259
  have hstep := st307_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p261 : ((1841594130333/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT307 (i+1))
      = (∑ i ∈ Finset.range 260, stT307 (i+1)) + stT307 261 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 260
    simpa using h
  have hprev := st307_p260
  have hstep := st307_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p262 : ((9789851172177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT307 (i+1))
      = (∑ i ∈ Finset.range 261, stT307 (i+1)) + stT307 262 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 261
    simpa using h
  have hprev := st307_p261
  have hstep := st307_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p263 : ((9826083499311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT307 (i+1))
      = (∑ i ∈ Finset.range 262, stT307 (i+1)) + stT307 263 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 262
    simpa using h
  have hprev := st307_p262
  have hstep := st307_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p264 : ((9275800039679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT307 (i+1))
      = (∑ i ∈ Finset.range 263, stT307 (i+1)) + stT307 264 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 263
    simpa using h
  have hprev := st307_p263
  have hstep := st307_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p265 : ((8804352431519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT307 (i+1))
      = (∑ i ∈ Finset.range 264, stT307 (i+1)) + stT307 265 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 264
    simpa using h
  have hprev := st307_p264
  have hstep := st307_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p266 : ((1794935753377/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT307 (i+1))
      = (∑ i ∈ Finset.range 265, stT307 (i+1)) + stT307 266 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 265
    simpa using h
  have hprev := st307_p265
  have hstep := st307_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p267 : ((1916170605183/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT307 (i+1))
      = (∑ i ∈ Finset.range 266, stT307 (i+1)) + stT307 267 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 266
    simpa using h
  have hprev := st307_p266
  have hstep := st307_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p268 : ((9905460786797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT307 (i+1))
      = (∑ i ∈ Finset.range 267, stT307 (i+1)) + stT307 268 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 267
    simpa using h
  have hprev := st307_p267
  have hstep := st307_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p269 : ((1913945660467/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT307 (i+1))
      = (∑ i ∈ Finset.range 268, stT307 (i+1)) + stT307 269 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 268
    simpa using h
  have hprev := st307_p268
  have hstep := st307_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p270 : ((896804556797/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT307 (i+1))
      = (∑ i ∈ Finset.range 269, stT307 (i+1)) + stT307 270 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 269
    simpa using h
  have hprev := st307_p269
  have hstep := st307_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p271 : ((1759499795587/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT307 (i+1))
      = (∑ i ∈ Finset.range 270, stT307 (i+1)) + stT307 271 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 270
    simpa using h
  have hprev := st307_p270
  have hstep := st307_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p272 : ((14802353681/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT307 (i+1))
      = (∑ i ∈ Finset.range 271, stT307 (i+1)) + stT307 272 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 271
    simpa using h
  have hprev := st307_p271
  have hstep := st307_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p273 : ((9808373095583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT307 (i+1))
      = (∑ i ∈ Finset.range 272, stT307 (i+1)) + stT307 273 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 272
    simpa using h
  have hprev := st307_p272
  have hstep := st307_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p274 : ((9836221911539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT307 (i+1))
      = (∑ i ∈ Finset.range 273, stT307 (i+1)) + stT307 274 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 273
    simpa using h
  have hprev := st307_p273
  have hstep := st307_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p275 : ((58166043193/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT307 (i+1))
      = (∑ i ∈ Finset.range 274, stT307 (i+1)) + stT307 275 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 274
    simpa using h
  have hprev := st307_p274
  have hstep := st307_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p276 : ((881511213343/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT307 (i+1))
      = (∑ i ∈ Finset.range 275, stT307 (i+1)) + stT307 276 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 275
    simpa using h
  have hprev := st307_p275
  have hstep := st307_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p277 : ((4453975840693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT307 (i+1))
      = (∑ i ∈ Finset.range 276, stT307 (i+1)) + stT307 277 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 276
    simpa using h
  have hprev := st307_p276
  have hstep := st307_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p278 : ((4739599845373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT307 (i+1))
      = (∑ i ∈ Finset.range 277, stT307 (i+1)) + stT307 278 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 277
    simpa using h
  have hprev := st307_p277
  have hstep := st307_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p279 : ((4949608314287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT307 (i+1))
      = (∑ i ∈ Finset.range 278, stT307 (i+1)) + stT307 279 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 278
    simpa using h
  have hprev := st307_p278
  have hstep := st307_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p280 : ((9710780850079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT307 (i+1))
      = (∑ i ∈ Finset.range 279, stT307 (i+1)) + stT307 280 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 279
    simpa using h
  have hprev := st307_p279
  have hstep := st307_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p281 : ((9121384081129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT307 (i+1))
      = (∑ i ∈ Finset.range 280, stT307 (i+1)) + stT307 281 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 280
    simpa using h
  have hprev := st307_p280
  have hstep := st307_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p282 : ((8767674933953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT307 (i+1))
      = (∑ i ∈ Finset.range 281, stT307 (i+1)) + stT307 282 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 281
    simpa using h
  have hprev := st307_p281
  have hstep := st307_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p283 : ((1805325873091/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT307 (i+1))
      = (∑ i ∈ Finset.range 282, stT307 (i+1)) + stT307 283 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 282
    simpa using h
  have hprev := st307_p282
  have hstep := st307_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p284 : ((1923910592183/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT307 (i+1))
      = (∑ i ∈ Finset.range 283, stT307 (i+1)) + stT307 284 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 283
    simpa using h
  have hprev := st307_p283
  have hstep := st307_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p285 : ((9918310190543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT307 (i+1))
      = (∑ i ∈ Finset.range 284, stT307 (i+1)) + stT307 285 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 284
    simpa using h
  have hprev := st307_p284
  have hstep := st307_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p286 : ((192218192461/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT307 (i+1))
      = (∑ i ∈ Finset.range 285, stT307 (i+1)) + stT307 286 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 285
    simpa using h
  have hprev := st307_p285
  have hstep := st307_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p287 : ((902122971069/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT307 (i+1))
      = (∑ i ∈ Finset.range 286, stT307 (i+1)) + stT307 287 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 286
    simpa using h
  have hprev := st307_p286
  have hstep := st307_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p288 : ((4380932278749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT307 (i+1))
      = (∑ i ∈ Finset.range 287, stT307 (i+1)) + stT307 288 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 287
    simpa using h
  have hprev := st307_p287
  have hstep := st307_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p289 : ((284313887169/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT307 (i+1))
      = (∑ i ∈ Finset.range 288, stT307 (i+1)) + stT307 289 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 288
    simpa using h
  have hprev := st307_p288
  have hstep := st307_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p290 : ((2420595137997/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT307 (i+1))
      = (∑ i ∈ Finset.range 289, stT307 (i+1)) + stT307 290 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 289
    simpa using h
  have hprev := st307_p289
  have hstep := st307_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p291 : ((1239893113611/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT307 (i+1))
      = (∑ i ∈ Finset.range 290, stT307 (i+1)) + stT307 291 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 290
    simpa using h
  have hprev := st307_p290
  have hstep := st307_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p292 : ((957086365443/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT307 (i+1))
      = (∑ i ∈ Finset.range 291, stT307 (i+1)) + stT307 292 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 291
    simpa using h
  have hprev := st307_p291
  have hstep := st307_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p293 : ((8990530531047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT307 (i+1))
      = (∑ i ∈ Finset.range 292, stT307 (i+1)) + stT307 293 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 292
    simpa using h
  have hprev := st307_p292
  have hstep := st307_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p294 : ((8758682182203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT307 (i+1))
      = (∑ i ∈ Finset.range 293, stT307 (i+1)) + stT307 294 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 293
    simpa using h
  have hprev := st307_p293
  have hstep := st307_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p295 : ((9103388463969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT307 (i+1))
      = (∑ i ∈ Finset.range 294, stT307 (i+1)) + stT307 295 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 294
    simpa using h
  have hprev := st307_p294
  have hstep := st307_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p296 : ((9681556364853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT307 (i+1))
      = (∑ i ∈ Finset.range 295, stT307 (i+1)) + stT307 296 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 295
    simpa using h
  have hprev := st307_p295
  have hstep := st307_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p297 : ((9925250218403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT307 (i+1))
      = (∑ i ∈ Finset.range 296, stT307 (i+1)) + stT307 297 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 296
    simpa using h
  have hprev := st307_p296
  have hstep := st307_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p298 : ((9598872939413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT307 (i+1))
      = (∑ i ∈ Finset.range 297, stT307 (i+1)) + stT307 298 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 297
    simpa using h
  have hprev := st307_p297
  have hstep := st307_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p299 : ((9021409219093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT307 (i+1))
      = (∑ i ∈ Finset.range 298, stT307 (i+1)) + stT307 299 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 298
    simpa using h
  have hprev := st307_p298
  have hstep := st307_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p300 : ((8749799059951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT307 (i+1))
      = (∑ i ∈ Finset.range 299, stT307 (i+1)) + stT307 300 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 299
    simpa using h
  have hprev := st307_p299
  have hstep := st307_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p301 : ((9042097956751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT307 (i+1))
      = (∑ i ∈ Finset.range 300, stT307 (i+1)) + stT307 301 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 300
    simpa using h
  have hprev := st307_p300
  have hstep := st307_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p302 : ((9617353421031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT307 (i+1))
      = (∑ i ∈ Finset.range 301, stT307 (i+1)) + stT307 302 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 301
    simpa using h
  have hprev := st307_p301
  have hstep := st307_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p303 : ((397217681227/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT307 (i+1))
      = (∑ i ∈ Finset.range 302, stT307 (i+1)) + stT307 303 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 302
    simpa using h
  have hprev := st307_p302
  have hstep := st307_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p304 : ((1937734051691/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT307 (i+1))
      = (∑ i ∈ Finset.range 303, stT307 (i+1)) + stT307 304 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 303
    simpa using h
  have hprev := st307_p303
  have hstep := st307_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p305 : ((9120666938029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT307 (i+1))
      = (∑ i ∈ Finset.range 304, stT307 (i+1)) + stT307 305 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 304
    simpa using h
  have hprev := st307_p304
  have hstep := st307_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p306 : ((1751042742269/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT307 (i+1))
      = (∑ i ∈ Finset.range 305, stT307 (i+1)) + stT307 306 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 305
    simpa using h
  have hprev := st307_p305
  have hstep := st307_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p307 : ((1785655005557/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT307 (i+1))
      = (∑ i ∈ Finset.range 306, stT307 (i+1)) + stT307 307 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 306
    simpa using h
  have hprev := st307_p306
  have hstep := st307_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p308 : ((9478241650363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT307 (i+1))
      = (∑ i ∈ Finset.range 307, stT307 (i+1)) + stT307 308 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 307
    simpa using h
  have hprev := st307_p307
  have hstep := st307_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p309 : ((9901761432763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT307 (i+1))
      = (∑ i ∈ Finset.range 308, stT307 (i+1)) + stT307 309 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 308
    simpa using h
  have hprev := st307_p308
  have hstep := st307_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p310 : ((9815699286827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT307 (i+1))
      = (∑ i ∈ Finset.range 309, stT307 (i+1)) + stT307 310 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 309
    simpa using h
  have hprev := st307_p309
  have hstep := st307_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p311 : ((1860044406847/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT307 (i+1))
      = (∑ i ∈ Finset.range 310, stT307 (i+1)) + stT307 311 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 310
    simpa using h
  have hprev := st307_p310
  have hstep := st307_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p312 : ((8819153344931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT307 (i+1))
      = (∑ i ∈ Finset.range 311, stT307 (i+1)) + stT307 312 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 311
    simpa using h
  have hprev := st307_p311
  have hstep := st307_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p313 : ((8800507405739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT307 (i+1))
      = (∑ i ∈ Finset.range 312, stT307 (i+1)) + stT307 313 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 312
    simpa using h
  have hprev := st307_p312
  have hstep := st307_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p314 : ((9258294088471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT307 (i+1))
      = (∑ i ∈ Finset.range 313, stT307 (i+1)) + stT307 314 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 313
    simpa using h
  have hprev := st307_p313
  have hstep := st307_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p315 : ((9787175685463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT307 (i+1))
      = (∑ i ∈ Finset.range 314, stT307 (i+1)) + stT307 315 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 314
    simpa using h
  have hprev := st307_p314
  have hstep := st307_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p316 : ((9924104277093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT307 (i+1))
      = (∑ i ∈ Finset.range 315, stT307 (i+1)) + stT307 316 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 315
    simpa using h
  have hprev := st307_p315
  have hstep := st307_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p317 : ((9552021780149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT307 (i+1))
      = (∑ i ∈ Finset.range 316, stT307 (i+1)) + stT307 317 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 316
    simpa using h
  have hprev := st307_p316
  have hstep := st307_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p318 : ((4497616536157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT307 (i+1))
      = (∑ i ∈ Finset.range 317, stT307 (i+1)) + stT307 318 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 317
    simpa using h
  have hprev := st307_p317
  have hstep := st307_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p319 : ((873327705419/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT307 (i+1))
      = (∑ i ∈ Finset.range 318, stT307 (i+1)) + stT307 319 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 318
    simpa using h
  have hprev := st307_p318
  have hstep := st307_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p320 : ((898842593199/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT307 (i+1))
      = (∑ i ∈ Finset.range 319, stT307 (i+1)) + stT307 320 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 319
    simpa using h
  have hprev := st307_p319
  have hstep := st307_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p321 : ((1908229264147/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT307 (i+1))
      = (∑ i ∈ Finset.range 320, stT307 (i+1)) + stT307 321 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 320
    simpa using h
  have hprev := st307_p320
  have hstep := st307_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p322 : ((396914824207/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT307 (i+1))
      = (∑ i ∈ Finset.range 321, stT307 (i+1)) + stT307 322 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 321
    simpa using h
  have hprev := st307_p321
  have hstep := st307_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p323 : ((1962756421187/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT307 (i+1))
      = (∑ i ∈ Finset.range 322, stT307 (i+1)) + stT307 323 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 322
    simpa using h
  have hprev := st307_p322
  have hstep := st307_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p324 : ((9307493923127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT307 (i+1))
      = (∑ i ∈ Finset.range 323, stT307 (i+1)) + stT307 324 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 323
    simpa using h
  have hprev := st307_p323
  have hstep := st307_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p325 : ((8826468309947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT307 (i+1))
      = (∑ i ∈ Finset.range 324, stT307 (i+1)) + stT307 325 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 324
    simpa using h
  have hprev := st307_p324
  have hstep := st307_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p326 : ((8767734838893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT307 (i+1))
      = (∑ i ∈ Finset.range 325, stT307 (i+1)) + stT307 326 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 325
    simpa using h
  have hprev := st307_p325
  have hstep := st307_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p327 : ((2294323918627/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT307 (i+1))
      = (∑ i ∈ Finset.range 326, stT307 (i+1)) + stT307 327 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 326
    simpa using h
  have hprev := st307_p326
  have hstep := st307_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p328 : ((9718307385463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT307 (i+1))
      = (∑ i ∈ Finset.range 327, stT307 (i+1)) + stT307 328 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 327
    simpa using h
  have hprev := st307_p327
  have hstep := st307_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p329 : ((4975415146033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT307 (i+1))
      = (∑ i ∈ Finset.range 328, stT307 (i+1)) + stT307 329 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 328
    simpa using h
  have hprev := st307_p328
  have hstep := st307_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p330 : ((4844344280869/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT307 (i+1))
      = (∑ i ∈ Finset.range 329, stT307 (i+1)) + stT307 330 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 329
    simpa using h
  have hprev := st307_p329
  have hstep := st307_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p331 : ((4572403294419/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT307 (i+1))
      = (∑ i ∈ Finset.range 330, stT307 (i+1)) + stT307 331 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 330
    simpa using h
  have hprev := st307_p330
  have hstep := st307_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p332 : ((4377372262033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT307 (i+1))
      = (∑ i ∈ Finset.range 331, stT307 (i+1)) + stT307 332 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 331
    simpa using h
  have hprev := st307_p331
  have hstep := st307_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p333 : ((882731234637/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT307 (i+1))
      = (∑ i ∈ Finset.range 332, stT307 (i+1)) + stT307 333 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 332
    simpa using h
  have hprev := st307_p332
  have hstep := st307_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p334 : ((1860565533369/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT307 (i+1))
      = (∑ i ∈ Finset.range 333, stT307 (i+1)) + stT307 334 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 333
    simpa using h
  have hprev := st307_p333
  have hstep := st307_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p335 : ((1961180637217/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT307 (i+1))
      = (∑ i ∈ Finset.range 334, stT307 (i+1)) + stT307 335 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 334
    simpa using h
  have hprev := st307_p334
  have hstep := st307_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p336 : ((9943610493653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT307 (i+1))
      = (∑ i ∈ Finset.range 335, stT307 (i+1)) + stT307 336 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 335
    simpa using h
  have hprev := st307_p335
  have hstep := st307_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p337 : ((4805418937119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT307 (i+1))
      = (∑ i ∈ Finset.range 336, stT307 (i+1)) + stT307 337 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 336
    simpa using h
  have hprev := st307_p336
  have hstep := st307_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p338 : ((9066859376699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT307 (i+1))
      = (∑ i ∈ Finset.range 337, stT307 (i+1)) + stT307 338 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 337
    simpa using h
  have hprev := st307_p337
  have hstep := st307_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p339 : ((8730402052841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT307 (i+1))
      = (∑ i ∈ Finset.range 338, stT307 (i+1)) + stT307 339 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 338
    simpa using h
  have hprev := st307_p338
  have hstep := st307_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p340 : ((1771463328207/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT307 (i+1))
      = (∑ i ∈ Finset.range 339, stT307 (i+1)) + stT307 340 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 339
    simpa using h
  have hprev := st307_p339
  have hstep := st307_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p341 : ((1869768243861/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT307 (i+1))
      = (∑ i ∈ Finset.range 340, stT307 (i+1)) + stT307 341 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 340
    simpa using h
  have hprev := st307_p340
  have hstep := st307_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p342 : ((9831843000831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT307 (i+1))
      = (∑ i ∈ Finset.range 341, stT307 (i+1)) + stT307 342 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 341
    simpa using h
  have hprev := st307_p341
  have hstep := st307_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p343 : ((4971736838469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT307 (i+1))
      = (∑ i ∈ Finset.range 342, stT307 (i+1)) + stT307 343 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 342
    simpa using h
  have hprev := st307_p342
  have hstep := st307_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p344 : ((4801070944237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT307 (i+1))
      = (∑ i ∈ Finset.range 343, stT307 (i+1)) + stT307 344 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 343
    simpa using h
  have hprev := st307_p343
  have hstep := st307_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p345 : ((566482200173/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT307 (i+1))
      = (∑ i ∈ Finset.range 344, stT307 (i+1)) + stT307 345 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 344
    simpa using h
  have hprev := st307_p344
  have hstep := st307_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p346 : ((2181772136131/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT307 (i+1))
      = (∑ i ∈ Finset.range 345, stT307 (i+1)) + stT307 346 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 345
    simpa using h
  have hprev := st307_p345
  have hstep := st307_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p347 : ((1104835610749/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT307 (i+1))
      = (∑ i ∈ Finset.range 346, stT307 (i+1)) + stT307 347 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 346
    simpa using h
  have hprev := st307_p346
  have hstep := st307_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p348 : ((1164330724007/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT307 (i+1))
      = (∑ i ∈ Finset.range 347, stT307 (i+1)) + stT307 348 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 347
    simpa using h
  have hprev := st307_p347
  have hstep := st307_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p349 : ((1961394880889/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT307 (i+1))
      = (∑ i ∈ Finset.range 348, stT307 (i+1)) + stT307 349 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 348
    simpa using h
  have hprev := st307_p348
  have hstep := st307_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p350 : ((9959411526493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT307 (i+1))
      = (∑ i ∈ Finset.range 349, stT307 (i+1)) + stT307 350 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 349
    simpa using h
  have hprev := st307_p349
  have hstep := st307_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p351 : ((4831952445151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT307 (i+1))
      = (∑ i ∈ Finset.range 350, stT307 (i+1)) + stT307 351 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 350
    simpa using h
  have hprev := st307_p350
  have hstep := st307_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p352 : ((913411902437/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT307 (i+1))
      = (∑ i ∈ Finset.range 351, stT307 (i+1)) + stT307 352 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 351
    simpa using h
  have hprev := st307_p351
  have hstep := st307_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p353 : ((8748316060691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT307 (i+1))
      = (∑ i ∈ Finset.range 352, stT307 (i+1)) + stT307 353 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 352
    simpa using h
  have hprev := st307_p352
  have hstep := st307_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p354 : ((8778961473237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT307 (i+1))
      = (∑ i ∈ Finset.range 353, stT307 (i+1)) + stT307 354 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 353
    simpa using h
  have hprev := st307_p353
  have hstep := st307_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p355 : ((9202380544533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT307 (i+1))
      = (∑ i ∈ Finset.range 354, stT307 (i+1)) + stT307 355 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 354
    simpa using h
  have hprev := st307_p354
  have hstep := st307_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p356 : ((9719944791453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT307 (i+1))
      = (∑ i ∈ Finset.range 355, stT307 (i+1)) + stT307 356 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 355
    simpa using h
  have hprev := st307_p355
  have hstep := st307_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p357 : ((9970415193453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT307 (i+1))
      = (∑ i ∈ Finset.range 356, stT307 (i+1)) + stT307 357 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 356
    simpa using h
  have hprev := st307_p356
  have hstep := st307_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p358 : ((9781387917301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT307 (i+1))
      = (∑ i ∈ Finset.range 357, stT307 (i+1)) + stT307 358 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 357
    simpa using h
  have hprev := st307_p357
  have hstep := st307_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p359 : ((9285336467561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT307 (i+1))
      = (∑ i ∈ Finset.range 358, stT307 (i+1)) + stT307 359 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 358
    simpa using h
  have hprev := st307_p358
  have hstep := st307_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p360 : ((2206017946193/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT307 (i+1))
      = (∑ i ∈ Finset.range 359, stT307 (i+1)) + stT307 360 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 359
    simpa using h
  have hprev := st307_p359
  have hstep := st307_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p361 : ((217805780343/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT307 (i+1))
      = (∑ i ∈ Finset.range 360, stT307 (i+1)) + stT307 361 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 360
    simpa using h
  have hprev := st307_p360
  have hstep := st307_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p362 : ((45120207753/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT307 (i+1))
      = (∑ i ∈ Finset.range 361, stT307 (i+1)) + stT307 362 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 361
    simpa using h
  have hprev := st307_p361
  have hstep := st307_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p363 : ((9546789877573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT307 (i+1))
      = (∑ i ∈ Finset.range 362, stT307 (i+1)) + stT307 363 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 362
    simpa using h
  have hprev := st307_p362
  have hstep := st307_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p364 : ((9928139872513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT307 (i+1))
      = (∑ i ∈ Finset.range 363, stT307 (i+1)) + stT307 364 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 363
    simpa using h
  have hprev := st307_p363
  have hstep := st307_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p365 : ((1982756261069/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT307 (i+1))
      = (∑ i ∈ Finset.range 364, stT307 (i+1)) + stT307 365 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 364
    simpa using h
  have hprev := st307_p364
  have hstep := st307_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p366 : ((1189390396669/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT307 (i+1))
      = (∑ i ∈ Finset.range 365, stT307 (i+1)) + stT307 366 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 365
    simpa using h
  have hprev := st307_p365
  have hstep := st307_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p367 : ((449888203191/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT307 (i+1))
      = (∑ i ∈ Finset.range 366, stT307 (i+1)) + stT307 367 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 366
    simpa using h
  have hprev := st307_p366
  have hstep := st307_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p368 : ((8702821443081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT307 (i+1))
      = (∑ i ∈ Finset.range 367, stT307 (i+1)) + stT307 368 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 367
    simpa using h
  have hprev := st307_p367
  have hstep := st307_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p369 : ((2205594013621/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT307 (i+1))
      = (∑ i ∈ Finset.range 368, stT307 (i+1)) + stT307 369 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 368
    simpa using h
  have hprev := st307_p368
  have hstep := st307_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p370 : ((9276522738359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT307 (i+1))
      = (∑ i ∈ Finset.range 369, stT307 (i+1)) + stT307 370 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 369
    simpa using h
  have hprev := st307_p369
  have hstep := st307_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p371 : ((9769209000053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT307 (i+1))
      = (∑ i ∈ Finset.range 370, stT307 (i+1)) + stT307 371 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 370
    simpa using h
  have hprev := st307_p370
  have hstep := st307_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p372 : ((1247803397191/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT307 (i+1))
      = (∑ i ∈ Finset.range 371, stT307 (i+1)) + stT307 372 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 371
    simpa using h
  have hprev := st307_p371
  have hstep := st307_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p373 : ((9780623586121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT307 (i+1))
      = (∑ i ∈ Finset.range 372, stT307 (i+1)) + stT307 373 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 372
    simpa using h
  have hprev := st307_p372
  have hstep := st307_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p374 : ((9294588788873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT307 (i+1))
      = (∑ i ∈ Finset.range 373, stT307 (i+1)) + stT307 374 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 373
    simpa using h
  have hprev := st307_p373
  have hstep := st307_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p375 : ((8834405875153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT307 (i+1))
      = (∑ i ∈ Finset.range 374, stT307 (i+1)) + stT307 375 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 374
    simpa using h
  have hprev := st307_p374
  have hstep := st307_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p376 : ((2172703470717/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT307 (i+1))
      = (∑ i ∈ Finset.range 375, stT307 (i+1)) + stT307 376 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 375
    simpa using h
  have hprev := st307_p375
  have hstep := st307_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p377 : ((1119075586103/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT307 (i+1))
      = (∑ i ∈ Finset.range 376, stT307 (i+1)) + stT307 377 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 376
    simpa using h
  have hprev := st307_p376
  have hstep := st307_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p378 : ((1181752774427/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT307 (i+1))
      = (∑ i ∈ Finset.range 377, stT307 (i+1)) + stT307 378 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 377
    simpa using h
  have hprev := st307_p377
  have hstep := st307_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p379 : ((9881678614151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT307 (i+1))
      = (∑ i ∈ Finset.range 378, stT307 (i+1)) + stT307 379 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 378
    simpa using h
  have hprev := st307_p378
  have hstep := st307_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p380 : ((1994183225727/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT307 (i+1))
      = (∑ i ∈ Finset.range 379, stT307 (i+1)) + stT307 380 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 379
    simpa using h
  have hprev := st307_p379
  have hstep := st307_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p381 : ((9668259303843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT307 (i+1))
      = (∑ i ∈ Finset.range 380, stT307 (i+1)) + stT307 381 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 380
    simpa using h
  have hprev := st307_p380
  have hstep := st307_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p382 : ((9161161804603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT307 (i+1))
      = (∑ i ∈ Finset.range 381, stT307 (i+1)) + stT307 382 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 381
    simpa using h
  have hprev := st307_p381
  have hstep := st307_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p383 : ((547505773779/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT307 (i+1))
      = (∑ i ∈ Finset.range 382, stT307 (i+1)) + stT307 383 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 382
    simpa using h
  have hprev := st307_p382
  have hstep := st307_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p384 : ((8708155478439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT307 (i+1))
      = (∑ i ∈ Finset.range 383, stT307 (i+1)) + stT307 384 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 383
    simpa using h
  have hprev := st307_p383
  have hstep := st307_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p385 : ((4517549307881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT307 (i+1))
      = (∑ i ∈ Finset.range 384, stT307 (i+1)) + stT307 385 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 384
    simpa using h
  have hprev := st307_p384
  have hstep := st307_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p386 : ((4771246253777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT307 (i+1))
      = (∑ i ∈ Finset.range 385, stT307 (i+1)) + stT307 386 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 385
    simpa using h
  have hprev := st307_p385
  have hstep := st307_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p387 : ((992579062769/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT307 (i+1))
      = (∑ i ∈ Finset.range 386, stT307 (i+1)) + stT307 387 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 386
    simpa using h
  have hprev := st307_p386
  have hstep := st307_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p388 : ((4978613885271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT307 (i+1))
      = (∑ i ∈ Finset.range 387, stT307 (i+1)) + stT307 388 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 387
    simpa using h
  have hprev := st307_p387
  have hstep := st307_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p389 : ((9619758142089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT307 (i+1))
      = (∑ i ∈ Finset.range 388, stT307 (i+1)) + stT307 389 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 388
    simpa using h
  have hprev := st307_p388
  have hstep := st307_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p390 : ((9114087945429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT307 (i+1))
      = (∑ i ∈ Finset.range 389, stT307 (i+1)) + stT307 390 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 389
    simpa using h
  have hprev := st307_p389
  have hstep := st307_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p391 : ((8737765033569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT307 (i+1))
      = (∑ i ∈ Finset.range 390, stT307 (i+1)) + stT307 391 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 390
    simpa using h
  have hprev := st307_p390
  have hstep := st307_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p392 : ((8709993879801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT307 (i+1))
      = (∑ i ∈ Finset.range 391, stT307 (i+1)) + stT307 392 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 391
    simpa using h
  have hprev := st307_p391
  have hstep := st307_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p393 : ((361812184761/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT307 (i+1))
      = (∑ i ∈ Finset.range 392, stT307 (i+1)) + stT307 393 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 392
    simpa using h
  have hprev := st307_p392
  have hstep := st307_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p394 : ((9548035633073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT307 (i+1))
      = (∑ i ∈ Finset.range 393, stT307 (i+1)) + stT307 394 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 393
    simpa using h
  have hprev := st307_p393
  have hstep := st307_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p395 : ((9927969734243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT307 (i+1))
      = (∑ i ∈ Finset.range 394, stT307 (i+1)) + stT307 395 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 394
    simpa using h
  have hprev := st307_p394
  have hstep := st307_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p396 : ((9967936498337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT307 (i+1))
      = (∑ i ∈ Finset.range 395, stT307 (i+1)) + stT307 396 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 395
    simpa using h
  have hprev := st307_p395
  have hstep := st307_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p397 : ((9646664213157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT307 (i+1))
      = (∑ i ∈ Finset.range 396, stT307 (i+1)) + stT307 397 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 396
    simpa using h
  have hprev := st307_p396
  have hstep := st307_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p398 : ((9148062857127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT307 (i+1))
      = (∑ i ∈ Finset.range 397, stT307 (i+1)) + stT307 398 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 397
    simpa using h
  have hprev := st307_p397
  have hstep := st307_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p399 : ((2188629367323/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT307 (i+1))
      = (∑ i ∈ Finset.range 398, stT307 (i+1)) + stT307 399 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 398
    simpa using h
  have hprev := st307_p398
  have hstep := st307_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p400 : ((4343371166871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT307 (i+1))
      = (∑ i ∈ Finset.range 399, stT307 (i+1)) + stT307 400 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 399
    simpa using h
  have hprev := st307_p399
  have hstep := st307_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p401 : ((4490585713543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT307 (i+1))
      = (∑ i ∈ Finset.range 400, stT307 (i+1)) + stT307 401 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 400
    simpa using h
  have hprev := st307_p400
  have hstep := st307_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p402 : ((2368053547873/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT307 (i+1))
      = (∑ i ∈ Finset.range 401, stT307 (i+1)) + stT307 402 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 401
    simpa using h
  have hprev := st307_p401
  have hstep := st307_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p403 : ((9886848315847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT307 (i+1))
      = (∑ i ∈ Finset.range 402, stT307 (i+1)) + stT307 403 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 402
    simpa using h
  have hprev := st307_p402
  have hstep := st307_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p404 : ((9996691334923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT307 (i+1))
      = (∑ i ∈ Finset.range 403, stT307 (i+1)) + stT307 404 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 403
    simpa using h
  have hprev := st307_p403
  have hstep := st307_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p405 : ((9742766931171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT307 (i+1))
      = (∑ i ∈ Finset.range 404, stT307 (i+1)) + stT307 405 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 404
    simpa using h
  have hprev := st307_p404
  have hstep := st307_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p406 : ((9265405989511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT307 (i+1))
      = (∑ i ∈ Finset.range 405, stT307 (i+1)) + stT307 406 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 405
    simpa using h
  have hprev := st307_p405
  have hstep := st307_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p407 : ((8825178413261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT307 (i+1))
      = (∑ i ∈ Finset.range 406, stT307 (i+1)) + stT307 407 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 406
    simpa using h
  have hprev := st307_p406
  have hstep := st307_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p408 : ((8660189061873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT307 (i+1))
      = (∑ i ∈ Finset.range 407, stT307 (i+1)) + stT307 408 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 407
    simpa using h
  have hprev := st307_p407
  have hstep := st307_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p409 : ((1771618393477/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT307 (i+1))
      = (∑ i ∈ Finset.range 408, stT307 (i+1)) + stT307 409 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 408
    simpa using h
  have hprev := st307_p408
  have hstep := st307_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p410 : ((9311128724369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT307 (i+1))
      = (∑ i ∈ Finset.range 409, stT307 (i+1)) + stT307 410 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 409
    simpa using h
  have hprev := st307_p409
  have hstep := st307_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p411 : ((9776325059669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT307 (i+1))
      = (∑ i ∈ Finset.range 410, stT307 (i+1)) + stT307 411 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 410
    simpa using h
  have hprev := st307_p410
  have hstep := st307_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p412 : ((10006436590133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT307 (i+1))
      = (∑ i ∈ Finset.range 411, stT307 (i+1)) + stT307 412 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 411
    simpa using h
  have hprev := st307_p411
  have hstep := st307_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p413 : ((9880773248429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT307 (i+1))
      = (∑ i ∈ Finset.range 412, stT307 (i+1)) + stT307 413 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 412
    simpa using h
  have hprev := st307_p412
  have hstep := st307_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p414 : ((1893401633693/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT307 (i+1))
      = (∑ i ∈ Finset.range 413, stT307 (i+1)) + stT307 414 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 413
    simpa using h
  have hprev := st307_p413
  have hstep := st307_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p415 : ((8983191927817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT307 (i+1))
      = (∑ i ∈ Finset.range 414, stT307 (i+1)) + stT307 415 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 414
    simpa using h
  have hprev := st307_p414
  have hstep := st307_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p416 : ((8681963020909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT307 (i+1))
      = (∑ i ∈ Finset.range 415, stT307 (i+1)) + stT307 416 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 415
    simpa using h
  have hprev := st307_p415
  have hstep := st307_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p417 : ((8718911526511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT307 (i+1))
      = (∑ i ∈ Finset.range 416, stT307 (i+1)) + stT307 417 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 416
    simpa using h
  have hprev := st307_p416
  have hstep := st307_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p418 : ((9073442621341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT307 (i+1))
      = (∑ i ∈ Finset.range 417, stT307 (i+1)) + stT307 418 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 417
    simpa using h
  have hprev := st307_p417
  have hstep := st307_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p419 : ((4780878112523/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT307 (i+1))
      = (∑ i ∈ Finset.range 418, stT307 (i+1)) + stT307 419 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 418
    simpa using h
  have hprev := st307_p418
  have hstep := st307_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p420 : ((1241644981937/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT307 (i+1))
      = (∑ i ∈ Finset.range 419, stT307 (i+1)) + stT307 420 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 419
    simpa using h
  have hprev := st307_p419
  have hstep := st307_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p421 : ((312462037523/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT307 (i+1))
      = (∑ i ∈ Finset.range 420, stT307 (i+1)) + stT307 421 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 420
    simpa using h
  have hprev := st307_p420
  have hstep := st307_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p422 : ((9726612906127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT307 (i+1))
      = (∑ i ∈ Finset.range 421, stT307 (i+1)) + stT307 422 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 421
    simpa using h
  have hprev := st307_p421
  have hstep := st307_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p423 : ((1851116481581/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT307 (i+1))
      = (∑ i ∈ Finset.range 422, stT307 (i+1)) + stT307 423 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 422
    simpa using h
  have hprev := st307_p422
  have hstep := st307_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p424 : ((8823416472493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT307 (i+1))
      = (∑ i ∈ Finset.range 423, stT307 (i+1)) + stT307 424 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 423
    simpa using h
  have hprev := st307_p423
  have hstep := st307_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p425 : ((8646299222701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT307 (i+1))
      = (∑ i ∈ Finset.range 424, stT307 (i+1)) + stT307 425 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 424
    simpa using h
  have hprev := st307_p424
  have hstep := st307_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p426 : ((8811401659469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT307 (i+1))
      = (∑ i ∈ Finset.range 425, stT307 (i+1)) + stT307 426 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 425
    simpa using h
  have hprev := st307_p425
  have hstep := st307_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p427 : ((9235315353077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT307 (i+1))
      = (∑ i ∈ Finset.range 426, stT307 (i+1)) + stT307 427 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 426
    simpa using h
  have hprev := st307_p426
  have hstep := st307_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p428 : ((9707509335021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT307 (i+1))
      = (∑ i ∈ Finset.range 427, stT307 (i+1)) + stT307 428 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 427
    simpa using h
  have hprev := st307_p427
  have hstep := st307_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p429 : ((9995537648517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT307 (i+1))
      = (∑ i ∈ Finset.range 428, stT307 (i+1)) + stT307 429 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 428
    simpa using h
  have hprev := st307_p428
  have hstep := st307_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p430 : ((2489786054009/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT307 (i+1))
      = (∑ i ∈ Finset.range 429, stT307 (i+1)) + stT307 430 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 429
    simpa using h
  have hprev := st307_p429
  have hstep := st307_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p431 : ((480871301301/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT307 (i+1))
      = (∑ i ∈ Finset.range 430, stT307 (i+1)) + stT307 431 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 430
    simpa using h
  have hprev := st307_p430
  have hstep := st307_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p432 : ((2284364163231/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT307 (i+1))
      = (∑ i ∈ Finset.range 431, stT307 (i+1)) + stT307 432 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 431
    simpa using h
  have hprev := st307_p431
  have hstep := st307_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p433 : ((4375837860717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT307 (i+1))
      = (∑ i ∈ Finset.range 432, stT307 (i+1)) + stT307 433 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 432
    simpa using h
  have hprev := st307_p432
  have hstep := st307_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p434 : ((4322606006381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT307 (i+1))
      = (∑ i ∈ Finset.range 433, stT307 (i+1)) + stT307 434 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 433
    simpa using h
  have hprev := st307_p433
  have hstep := st307_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p435 : ((4433924848943/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT307 (i+1))
      = (∑ i ∈ Finset.range 434, stT307 (i+1)) + stT307 435 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 434
    simpa using h
  have hprev := st307_p434
  have hstep := st307_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p436 : ((74496343537/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT307 (i+1))
      = (∑ i ∈ Finset.range 435, stT307 (i+1)) + stT307 436 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 435
    simpa using h
  have hprev := st307_p435
  have hstep := st307_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p437 : ((9766006551213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT307 (i+1))
      = (∑ i ∈ Finset.range 436, stT307 (i+1)) + stT307 437 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 436
    simpa using h
  have hprev := st307_p436
  have hstep := st307_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p438 : ((2003027597901/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT307 (i+1))
      = (∑ i ∈ Finset.range 437, stT307 (i+1)) + stT307 438 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 437
    simpa using h
  have hprev := st307_p437
  have hstep := st307_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p439 : ((9943053865463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT307 (i+1))
      = (∑ i ∈ Finset.range 438, stT307 (i+1)) + stT307 439 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 438
    simpa using h
  have hprev := st307_p438
  have hstep := st307_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p440 : ((9584837440663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT307 (i+1))
      = (∑ i ∈ Finset.range 439, stT307 (i+1)) + stT307 440 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 439
    simpa using h
  have hprev := st307_p439
  have hstep := st307_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p441 : ((9108734059807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT307 (i+1))
      = (∑ i ∈ Finset.range 440, stT307 (i+1)) + stT307 441 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 440
    simpa using h
  have hprev := st307_p440
  have hstep := st307_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p442 : ((8736306154239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT307 (i+1))
      = (∑ i ∈ Finset.range 441, stT307 (i+1)) + stT307 442 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 441
    simpa using h
  have hprev := st307_p441
  have hstep := st307_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p443 : ((4319654525707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT307 (i+1))
      = (∑ i ∈ Finset.range 442, stT307 (i+1)) + stT307 443 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 442
    simpa using h
  have hprev := st307_p442
  have hstep := st307_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p444 : ((4430618929933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT307 (i+1))
      = (∑ i ∈ Finset.range 443, stT307 (i+1)) + stT307 444 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 443
    simpa using h
  have hprev := st307_p443
  have hstep := st307_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p445 : ((2324755315409/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT307 (i+1))
      = (∑ i ∈ Finset.range 444, stT307 (i+1)) + stT307 445 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 444
    simpa using h
  have hprev := st307_p444
  have hstep := st307_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p446 : ((9751934078571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT307 (i+1))
      = (∑ i ∈ Finset.range 445, stT307 (i+1)) + stT307 446 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 445
    simpa using h
  have hprev := st307_p445
  have hstep := st307_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p447 : ((10014064095069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT307 (i+1))
      = (∑ i ∈ Finset.range 446, stT307 (i+1)) + stT307 447 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 446
    simpa using h
  have hprev := st307_p446
  have hstep := st307_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p448 : ((9967543715029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT307 (i+1))
      = (∑ i ∈ Finset.range 447, stT307 (i+1)) + stT307 448 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 447
    simpa using h
  have hprev := st307_p447
  have hstep := st307_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p449 : ((9634589077219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT307 (i+1))
      = (∑ i ∈ Finset.range 448, stT307 (i+1)) + stT307 449 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 448
    simpa using h
  have hprev := st307_p448
  have hstep := st307_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p450 : ((4582861767977/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT307 (i+1))
      = (∑ i ∈ Finset.range 449, stT307 (i+1)) + stT307 450 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 449
    simpa using h
  have hprev := st307_p449
  have hstep := st307_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p451 : ((4385472742397/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT307 (i+1))
      = (∑ i ∈ Finset.range 450, stT307 (i+1)) + stT307 451 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 450
    simpa using h
  have hprev := st307_p450
  have hstep := st307_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p452 : ((8625541377781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT307 (i+1))
      = (∑ i ∈ Finset.range 451, stT307 (i+1)) + stT307 452 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 451
    simpa using h
  have hprev := st307_p451
  have hstep := st307_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p453 : ((8792893217541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT307 (i+1))
      = (∑ i ∈ Finset.range 452, stT307 (i+1)) + stT307 453 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 452
    simpa using h
  have hprev := st307_p452
  have hstep := st307_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p454 : ((9197884236639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT307 (i+1))
      = (∑ i ∈ Finset.range 453, stT307 (i+1)) + stT307 454 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 453
    simpa using h
  have hprev := st307_p453
  have hstep := st307_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p455 : ((9661661875143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT307 (i+1))
      = (∑ i ∈ Finset.range 454, stT307 (i+1)) + stT307 455 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 454
    simpa using h
  have hprev := st307_p454
  have hstep := st307_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p456 : ((1996224824291/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT307 (i+1))
      = (∑ i ∈ Finset.range 455, stT307 (i+1)) + stT307 456 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 455
    simpa using h
  have hprev := st307_p455
  have hstep := st307_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p457 : ((2003542774611/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT307 (i+1))
      = (∑ i ∈ Finset.range 456, stT307 (i+1)) + stT307 457 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 456
    simpa using h
  have hprev := st307_p456
  have hstep := st307_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p458 : ((1951334417149/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT307 (i+1))
      = (∑ i ∈ Finset.range 457, stT307 (i+1)) + stT307 458 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 457
    simpa using h
  have hprev := st307_p457
  have hstep := st307_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p459 : ((9311908598153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT307 (i+1))
      = (∑ i ∈ Finset.range 458, stT307 (i+1)) + stT307 459 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 458
    simpa using h
  have hprev := st307_p458
  have hstep := st307_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p460 : ((443771036171/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT307 (i+1))
      = (∑ i ∈ Finset.range 459, stT307 (i+1)) + stT307 460 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 459
    simpa using h
  have hprev := st307_p459
  have hstep := st307_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p461 : ((8634089723647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT307 (i+1))
      = (∑ i ∈ Finset.range 460, stT307 (i+1)) + stT307 461 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 460
    simpa using h
  have hprev := st307_p460
  have hstep := st307_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p462 : ((8690028095517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT307 (i+1))
      = (∑ i ∈ Finset.range 461, stT307 (i+1)) + stT307 462 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 461
    simpa using h
  have hprev := st307_p461
  have hstep := st307_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p463 : ((9018280687041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT307 (i+1))
      = (∑ i ∈ Finset.range 462, stT307 (i+1)) + stT307 463 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 462
    simpa using h
  have hprev := st307_p462
  have hstep := st307_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p464 : ((9478906451163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT307 (i+1))
      = (∑ i ∈ Finset.range 463, stT307 (i+1)) + stT307 464 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 463
    simpa using h
  have hprev := st307_p463
  have hstep := st307_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p465 : ((1975469007929/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT307 (i+1))
      = (∑ i ∈ Finset.range 464, stT307 (i+1)) + stT307 465 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 464
    simpa using h
  have hprev := st307_p464
  have hstep := st307_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p466 : ((125583795413/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT307 (i+1))
      = (∑ i ∈ Finset.range 465, stT307 (i+1)) + stT307 466 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 465
    simpa using h
  have hprev := st307_p465
  have hstep := st307_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p467 : ((1983425618373/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT307 (i+1))
      = (∑ i ∈ Finset.range 466, stT307 (i+1)) + stT307 467 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 466
    simpa using h
  have hprev := st307_p466
  have hstep := st307_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p468 : ((4771842145867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT307 (i+1))
      = (∑ i ∈ Finset.range 467, stT307 (i+1)) + stT307 468 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 467
    simpa using h
  have hprev := st307_p467
  have hstep := st307_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p469 : ((2270505699789/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT307 (i+1))
      = (∑ i ∈ Finset.range 468, stT307 (i+1)) + stT307 469 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 468
    simpa using h
  have hprev := st307_p468
  have hstep := st307_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p470 : ((436147375693/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT307 (i+1))
      = (∑ i ∈ Finset.range 469, stT307 (i+1)) + stT307 470 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 469
    simpa using h
  have hprev := st307_p469
  have hstep := st307_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p471 : ((2153394315431/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT307 (i+1))
      = (∑ i ∈ Finset.range 470, stT307 (i+1)) + stT307 471 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 470
    simpa using h
  have hprev := st307_p470
  have hstep := st307_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p472 : ((8797668587087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT307 (i+1))
      = (∑ i ∈ Finset.range 471, stT307 (i+1)) + stT307 472 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 471
    simpa using h
  have hprev := st307_p471
  have hstep := st307_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p473 : ((9199024788487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT307 (i+1))
      = (∑ i ∈ Finset.range 472, stT307 (i+1)) + stT307 473 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 472
    simpa using h
  have hprev := st307_p472
  have hstep := st307_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p474 : ((9653870653537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT307 (i+1))
      = (∑ i ∈ Finset.range 473, stT307 (i+1)) + stT307 474 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 473
    simpa using h
  have hprev := st307_p473
  have hstep := st307_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p475 : ((4989052936921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT307 (i+1))
      = (∑ i ∈ Finset.range 474, stT307 (i+1)) + stT307 475 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 474
    simpa using h
  have hprev := st307_p474
  have hstep := st307_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p476 : ((2510423157653/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT307 (i+1))
      = (∑ i ∈ Finset.range 475, stT307 (i+1)) + stT307 476 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 475
    simpa using h
  have hprev := st307_p475
  have hstep := st307_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p477 : ((9820130279381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT307 (i+1))
      = (∑ i ∈ Finset.range 476, stT307 (i+1)) + stT307 477 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 476
    simpa using h
  have hprev := st307_p476
  have hstep := st307_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p478 : ((9402980994191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT307 (i+1))
      = (∑ i ∈ Finset.range 477, stT307 (i+1)) + stT307 478 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 477
    simpa using h
  have hprev := st307_p477
  have hstep := st307_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p479 : ((1791381572131/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT307 (i+1))
      = (∑ i ∈ Finset.range 478, stT307 (i+1)) + stT307 479 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 478
    simpa using h
  have hprev := st307_p478
  have hstep := st307_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p480 : ((8658717765419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT307 (i+1))
      = (∑ i ∈ Finset.range 479, stT307 (i+1)) + stT307 480 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 479
    simpa using h
  have hprev := st307_p479
  have hstep := st307_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p481 : ((8625459058157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT307 (i+1))
      = (∑ i ∈ Finset.range 480, stT307 (i+1)) + stT307 481 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 480
    simpa using h
  have hprev := st307_p480
  have hstep := st307_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p482 : ((354766950173/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT307 (i+1))
      = (∑ i ∈ Finset.range 481, stT307 (i+1)) + stT307 482 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 481
    simpa using h
  have hprev := st307_p481
  have hstep := st307_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p483 : ((1858675573723/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT307 (i+1))
      = (∑ i ∈ Finset.range 482, stT307 (i+1)) + stT307 483 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 482
    simpa using h
  have hprev := st307_p482
  have hstep := st307_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p484 : ((389279788109/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT307 (i+1))
      = (∑ i ∈ Finset.range 483, stT307 (i+1)) + stT307 484 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 483
    simpa using h
  have hprev := st307_p483
  have hstep := st307_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p485 : ((2002930494393/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT307 (i+1))
      = (∑ i ∈ Finset.range 484, stT307 (i+1)) + stT307 485 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 484
    simpa using h
  have hprev := st307_p484
  have hstep := st307_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p486 : ((627037866411/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT307 (i+1))
      = (∑ i ∈ Finset.range 485, stT307 (i+1)) + stT307 486 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 485
    simpa using h
  have hprev := st307_p485
  have hstep := st307_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p487 : ((1222492672239/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT307 (i+1))
      = (∑ i ∈ Finset.range 486, stT307 (i+1)) + stT307 487 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 486
    simpa using h
  have hprev := st307_p486
  have hstep := st307_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p488 : ((584663440863/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT307 (i+1))
      = (∑ i ∈ Finset.range 487, stT307 (i+1)) + stT307 488 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 487
    simpa using h
  have hprev := st307_p487
  have hstep := st307_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p489 : ((1114975888591/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT307 (i+1))
      = (∑ i ∈ Finset.range 488, stT307 (i+1)) + stT307 489 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 488
    simpa using h
  have hprev := st307_p488
  have hstep := st307_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p490 : ((864104010567/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT307 (i+1))
      = (∑ i ∈ Finset.range 489, stT307 (i+1)) + stT307 490 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 489
    simpa using h
  have hprev := st307_p489
  have hstep := st307_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p491 : ((4311703121957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT307 (i+1))
      = (∑ i ∈ Finset.range 490, stT307 (i+1)) + stT307 491 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 490
    simpa using h
  have hprev := st307_p490
  have hstep := st307_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p492 : ((1109068886021/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT307 (i+1))
      = (∑ i ∈ Finset.range 491, stT307 (i+1)) + stT307 492 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 491
    simpa using h
  have hprev := st307_p491
  have hstep := st307_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p493 : ((1161715255059/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT307 (i+1))
      = (∑ i ∈ Finset.range 492, stT307 (i+1)) + stT307 493 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 492
    simpa using h
  have hprev := st307_p492
  have hstep := st307_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p494 : ((38913775237/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT307 (i+1))
      = (∑ i ∈ Finset.range 493, stT307 (i+1)) + stT307 494 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 493
    simpa using h
  have hprev := st307_p493
  have hstep := st307_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p495 : ((1251799653089/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT307 (i+1))
      = (∑ i ∈ Finset.range 494, stT307 (i+1)) + stT307 495 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 494
    simpa using h
  have hprev := st307_p494
  have hstep := st307_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p496 : ((502290418907/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT307 (i+1))
      = (∑ i ∈ Finset.range 495, stT307 (i+1)) + stT307 496 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 495
    simpa using h
  have hprev := st307_p495
  have hstep := st307_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p497 : ((981198870721/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT307 (i+1))
      = (∑ i ∈ Finset.range 496, stT307 (i+1)) + stT307 497 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 496
    simpa using h
  have hprev := st307_p496
  have hstep := st307_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p498 : ((9400174250099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT307 (i+1))
      = (∑ i ∈ Finset.range 497, stT307 (i+1)) + stT307 498 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 497
    simpa using h
  have hprev := st307_p497
  have hstep := st307_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p499 : ((1792466611811/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT307 (i+1))
      = (∑ i ∈ Finset.range 498, stT307 (i+1)) + stT307 499 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 498
    simpa using h
  have hprev := st307_p498
  have hstep := st307_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_p500 : ((8658809811683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT307 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT307 (i+1))
      = (∑ i ∈ Finset.range 499, stT307 (i+1)) + stT307 500 := by
    have h := Finset.sum_range_succ (fun i => stT307 (i+1)) 499
    simpa using h
  have hprev := st307_p499
  have hstep := st307_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st307_s500 :
    |Real.sin (((307 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((56493/500000 : ℚ) : ℝ))
      - ((-73451/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -289581/500000) (δ := 1923/125000000) (ψ := 56493/500000) 307 304
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 307`** (evaluated boundary). -/
theorem station_307_sign : hardyG ((((307:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 307 500 (by norm_num) (by norm_num)
    ((56493/500000 : ℚ) : ℝ)
  have hchain := st307_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT307 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((307 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((56493/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st307_c500
  have hsinb := abs_le.mp st307_s500
  have hbdy_lo : ((100982090257347/1884985000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((307 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((56493/500000 : ℚ) : ℝ))) / 2
          - ((((307:ℕ)):ℝ))
            * Real.sin (((307 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((56493/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((307:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((307:ℝ) * Real.log (500:ℝ) - ((56493/500000 : ℚ) : ℝ))) / 2
        - ((307:ℝ)) * Real.sin ((307:ℝ) * Real.log (500:ℝ) - ((56493/500000 : ℚ) : ℝ))
        ≥ ((225803119/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((307:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((225803119/1000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((225803119/1000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((225803119/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((307:ℕ)):ℝ))+1) * (((((307:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((1834649148351/2500000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((8658809811683/10000000000000 : ℚ) : ℝ) + ((100982090257347/1884985000000000 : ℚ) : ℝ)
      - ((1834649148351/2500000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((56493/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((307:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((56493/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((307:ℕ)):ℝ)))).re
      - Real.sin ((56493/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((307:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((307:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((307:ℕ)):ℝ))
      = (((((307:ℕ)):ℝ)) * (Real.log ((((307:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((307:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_307
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
  have hθwin : |(((56493/500000 : ℚ) : ℝ) + ((71:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((307:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((307:ℕ)):ℝ)))
    (φ := ((56493/500000 : ℚ) : ℝ) + ((71:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((56493/500000 : ℚ) : ℝ) + ((71:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((56493/500000 : ℚ)) : ℝ) - Real.pi) + ((71:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((56493/500000 : ℚ)) : ℝ) - Real.pi) 71).1,
    (cos_sin_shift ((((56493/500000 : ℚ)) : ℝ) - Real.pi) 71).2]
  exact cos_sin_flip ((56493/500000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_307_sign
end AxiomAudit
