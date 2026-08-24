import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 174` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT174 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((174 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((501127/1000000 : ℚ) : ℝ))

theorem st174_c1 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((438521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -626409/5000000) (δ := 201/1000000000) (ψ := 501127/1000000) 174 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t1 : ((13703/15625 : ℚ) : ℝ) ≤ stT174 1 := by
  have hc : ((13703/15625 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13703/15625 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((13703/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c2 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((149573/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1814891/10000000) (δ := 4419/500000000) (ψ := 501127/1000000) 174 19
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t2 : ((1057569993721/2000000000000 : ℚ) : ℝ) ≤ stT174 2 := by
  have hc : ((149563/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1057569993721/2000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((149563/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c3 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-34827/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5404613/10000000) (δ := 4393/500000000) (ψ := 501127/1000000) 174 30
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t3 : ((-1608734649423/5000000000000 : ℚ) : ℝ) ≤ stT174 3 := by
  have hc : ((-278641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1608734649423/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-278641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c4 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-373011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4882621/10000000) (δ := 4437/500000000) (ψ := 501127/1000000) 174 38
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t4 : ((-1865305373061/10000000000000 : ℚ) : ℝ) ≤ stT174 4 := by
  have hc : ((-373061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1865305373061/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-373061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c5 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-12477/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7702307/10000000) (δ := 8717/1000000000) (ψ := 501127/1000000) 174 44
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t5 : ((-55801635957/125000000000 : ℚ) : ℝ) ≤ stT174 5 := by
  have hc : ((-99821/100000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55801635957/125000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-99821/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c6 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-484783/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -361781/500000) (δ := 219/25000000) (ψ := 501127/1000000) 174 50
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t6 : ((-247402552283/625000000000 : ℚ) : ℝ) ≤ stT174 6 := by
  have hc : ((-60601/62500 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-247402552283/625000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-60601/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c7 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((35791/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3011919/10000000) (δ := 4407/500000000) (ψ := 501127/1000000) 174 54
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t7 : ((16907292523/125000000000 : ℚ) : ℝ) ≤ stT174 7 := by
  have hc : ((17893/50000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16907292523/125000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((17893/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c8 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-999257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7757613/10000000) (δ := 1757/200000000) (ψ := 501127/1000000) 174 58
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t8 : ((-1766541937469/5000000000000 : ℚ) : ℝ) ≤ stT174 8 := by
  have hc : ((-999307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1766541937469/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-999307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c9 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((561/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1822949/5000000) (δ := 277/31250000) (ψ := 501127/1000000) 174 61
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t9 : ((7476665919/200000000000 : ℚ) : ℝ) ≤ stT174 9 := by
  have hc : ((2243/20000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7476665919/200000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((2243/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c10 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-19673/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -493797/1000000) (δ := 4371/500000000) (ψ := 501127/1000000) 174 64
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t10 : ((-62219400789/500000000000 : ℚ) : ℝ) ≤ stT174 10 := by
  have hc : ((-39351/100000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62219400789/500000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-39351/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c11 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-45433/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5106041/10000000) (δ := 71/8000000) (ψ := 501127/1000000) 174 66
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t11 : ((-34250187483/250000000000 : ℚ) : ℝ) ≤ stT174 11 := by
  have hc : ((-22719/50000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34250187483/250000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-22719/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c12 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-96211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -416789/1000000) (δ := 8797/1000000000) (ψ := 501127/1000000) 174 69
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t12 : ((-8683801071/312500000000 : ℚ) : ℝ) ≤ stT174 12 := by
  have hc : ((-96261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8683801071/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-96261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c13 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((953517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -382621/5000000) (δ := 8811/1000000000) (ψ := 501127/1000000) 174 71
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t13 : ((5288881449/20000000000 : ℚ) : ℝ) ≤ stT174 13 := by
  have hc : ((953467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5288881449/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((953467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c14 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((999751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55811/10000000) (δ := 8777/1000000000) (ψ := 501127/1000000) 174 73
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t14 : ((667953222253/2500000000000 : ℚ) : ℝ) ≤ stT174 14 := by
  have hc : ((999701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((667953222253/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((999701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c15 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((429039/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -337051/2500000) (δ := 8763/1000000000) (ψ := 501127/1000000) 174 75
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t15 : ((138463624979/625000000000 : ℚ) : ℝ) ≤ stT174 15 := by
  have hc : ((214507/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138463624979/625000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((214507/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c16 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-300443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4689883/10000000) (δ := 8749/1000000000) (ψ := 501127/1000000) 174 77
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t16 : ((-751232800493/10000000000000 : ℚ) : ℝ) ≤ stT174 16 := by
  have hc : ((-300493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-751232800493/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-300493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c17 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-73029/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1194771/2000000) (δ := 4381/500000000) (ψ := 501127/1000000) 174 78
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t17 : ((-88566761569/500000000000 : ℚ) : ℝ) ≤ stT174 17 := by
  have hc : ((-36517/50000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88566761569/500000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-36517/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c18 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((973377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72271/1250000) (δ := 8827/1000000000) (ψ := 501127/1000000) 174 80
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t18 : ((1147076576097/5000000000000 : ℚ) : ℝ) ≤ stT174 18 := by
  have hc : ((973327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1147076576097/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((973327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c19 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-969319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7233101/10000000) (δ := 109/12500000) (ψ := 501127/1000000) 174 81
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t19 : ((-1111942823151/5000000000000 : ℚ) : ℝ) ≤ stT174 19 := by
  have hc : ((-969369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1111942823151/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-969369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c20 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((146597/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11689/62500) (δ := 4353/500000000) (ψ := 501127/1000000) 174 83
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t20 : ((327778353329/2000000000000 : ℚ) : ℝ) ≤ stT174 20 := by
  have hc : ((146587/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((327778353329/2000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((146587/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c21 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((22469/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1822767/5000000) (δ := 1761/200000000) (ψ := 501127/1000000) 174 84
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t21 : ((24504767851/1000000000000 : ℚ) : ℝ) ≤ stT174 21 := by
  have hc : ((22459/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24504767851/1000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((22459/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c22 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-99183/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7534193/10000000) (δ := 549/62500000) (ψ := 501127/1000000) 174 86
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t22 : ((-6608425297/31250000000 : ℚ) : ℝ) ≤ stT174 22 := by
  have hc : ((-24797/25000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6608425297/31250000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-24797/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c23 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((8547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3905623/10000000) (δ := 4363/500000000) (ψ := 501127/1000000) 174 87
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t23 : ((2214683571/1250000000000 : ℚ) : ℝ) ≤ stT174 23 := by
  have hc : ((8497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2214683571/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((8497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c24 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((226181/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1719/15625) (δ := 8833/1000000000) (ψ := 501127/1000000) 174 88
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t24 : ((923328830217/5000000000000 : ℚ) : ℝ) ≤ stT174 24 := by
  have hc : ((452337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((923328830217/5000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((452337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c25 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((928747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 474723/5000000) (δ := 8863/1000000000) (ψ := 501127/1000000) 174 89
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t25 : ((928697/5000000 : ℚ) : ℝ) ≤ stT174 25 := by
  have hc : ((928697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((928697/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((928697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c26 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((151257/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 287811/1250000) (δ := 553/62500000) (ψ := 501127/1000000) 174 90
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t26 : ((593229629729/5000000000000 : ℚ) : ℝ) ≤ stT174 26 := by
  have hc : ((302489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((593229629729/5000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((302489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c27 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((179023/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 602311/2000000) (δ := 1751/200000000) (ψ := 501127/1000000) 174 91
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t27 : ((344481651/5000000000 : ℚ) : ℝ) ≤ stT174 27 := by
  have hc : ((89499/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((344481651/5000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((89499/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c28 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((78969/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3123541/10000000) (δ := 8741/1000000000) (ψ := 501127/1000000) 174 92
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t28 : ((149213730743/2500000000000 : ℚ) : ℝ) ≤ stT174 28 := by
  have hc : ((157913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149213730743/2500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((157913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c29 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((239133/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2680293/10000000) (δ := 4417/500000000) (ψ := 501127/1000000) 174 93
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t29 : ((111003079481/1250000000000 : ℚ) : ℝ) ≤ stT174 29 := by
  have hc : ((59777/125000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111003079481/1250000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((59777/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c30 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((772649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1719483/10000000) (δ := 2219/250000000) (ψ := 501127/1000000) 174 94
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t30 : ((1410565670859/10000000000000 : ℚ) : ℝ) ≤ stT174 30 := by
  have hc : ((772599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1410565670859/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((772599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c31 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((993951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 137563/5000000) (δ := 549/62500000) (ψ := 501127/1000000) 174 95
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t31 : ((1785098872753/10000000000000 : ℚ) : ℝ) ≤ stT174 31 := by
  have hc : ((993901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1785098872753/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((993901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c32 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((199193/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1622153/10000000) (δ := 1089/125000000) (ψ := 501127/1000000) 174 96
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t32 : ((352104515763/2500000000000 : ℚ) : ℝ) ≤ stT174 32 := by
  have hc : ((398361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352104515763/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((398361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c33 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-437/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -394447/1000000) (δ := 4399/500000000) (ψ := 501127/1000000) 174 97
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t33 : ((-6129275817/5000000000000 : ℚ) : ℝ) ≤ stT174 33 := by
  have hc : ((-3521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6129275817/5000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-3521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c34 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-444637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6666379/10000000) (δ := 4449/500000000) (ψ := 501127/1000000) 174 98
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t34 : ((-190647276183/1250000000000 : ℚ) : ℝ) ≤ stT174 34 := by
  have hc : ((-222331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190647276183/1250000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-222331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c35 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-360927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 371449/625000) (δ := 1741/200000000) (ψ := 501127/1000000) 174 98
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t35 : ((-76265051771/625000000000 : ℚ) : ℝ) ≤ stT174 35 := by
  have hc : ((-45119/62500 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76265051771/625000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-45119/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c36 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((543811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1244781/5000000) (δ := 8791/1000000000) (ψ := 501127/1000000) 174 99
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t36 : ((453133985413/5000000000000 : ℚ) : ℝ) ≤ stT174 36 := by
  have hc : ((543761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((453133985413/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((543761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c37 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((216963/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -324959/2500000) (δ := 8719/1000000000) (ψ := 501127/1000000) 174 100
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t37 : ((713328471089/5000000000000 : ℚ) : ℝ) ≤ stT174 37 := by
  have hc : ((433901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((713328471089/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((433901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c38 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-558069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1351783/2500000) (δ := 8827/1000000000) (ψ := 501127/1000000) 174 101
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t38 : ((-181077802717/2000000000000 : ℚ) : ℝ) ≤ stT174 38 := by
  have hc : ((-558119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181077802717/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-558119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c39 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-353797/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 589221/1000000) (δ := 1097/125000000) (ψ := 501127/1000000) 174 101
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t39 : ((-141642199951/1250000000000 : ℚ) : ℝ) ≤ stT174 39 := by
  have hc : ((-176911/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141642199951/1250000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-176911/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c40 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((443729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119749/1000000) (δ := 4367/500000000) (ψ := 501127/1000000) 174 102
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t40 : ((43847328447/312500000000 : ℚ) : ℝ) ≤ stT174 40 := by
  have hc : ((55463/62500 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43847328447/312500000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((55463/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c41 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((31539/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -471149/1250000) (δ := 8841/1000000000) (ψ := 501127/1000000) 174 103
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t41 : ((24608289909/2500000000000 : ℚ) : ℝ) ≤ stT174 41 := by
  have hc : ((15757/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24608289909/2500000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((15757/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c42 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-179539/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 419579/625000) (δ := 8841/1000000000) (ψ := 501127/1000000) 174 103
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t42 : ((-138525105833/1000000000000 : ℚ) : ℝ) ≤ stT174 42 := by
  have hc : ((-179549/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138525105833/1000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-179549/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c43 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((87929/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 310267/2500000) (δ := 2187/250000000) (ψ := 501127/1000000) 174 104
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t43 : ((6704139057/50000000000 : ℚ) : ℝ) ≤ stT174 43 := by
  have hc : ((21981/25000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6704139057/50000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((21981/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c44 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-107059/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4466463/10000000) (δ := 2187/250000000) (ψ := 501127/1000000) 174 105
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t44 : ((-40358808447/1250000000000 : ℚ) : ℝ) ≤ stT174 44 := by
  have hc : ((-26771/125000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40358808447/1250000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-26771/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c45 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-105029/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1061841/2000000) (δ := 2187/250000000) (ψ := 501127/1000000) 174 105
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t45 : ((-19572862221/250000000000 : ℚ) : ℝ) ≤ stT174 45 := by
  have hc : ((-105039/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19572862221/250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-105039/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c46 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((944353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -837937/10000000) (δ := 221/25000000) (ψ := 501127/1000000) 174 106
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t46 : ((1392298284957/10000000000000 : ℚ) : ℝ) ≤ stT174 46 := by
  have hc : ((944303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1392298284957/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((944303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c47 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-482503/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7190659/10000000) (δ := 887/100000000) (ψ := 501127/1000000) 174 107
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t47 : ((-439899667/3125000000 : ℚ) : ℝ) ≤ stT174 47 := by
  have hc : ((-15079/15625 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-439899667/3125000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-15079/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c48 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((705953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 196757/1000000) (δ := 887/100000000) (ψ := 501127/1000000) 174 107
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t48 : ((8151061941/80000000000 : ℚ) : ℝ) ≤ stT174 48 := by
  have hc : ((705903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8151061941/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((705903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c49 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-331243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2385521/5000000) (δ := 4413/500000000) (ψ := 501127/1000000) 174 108
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t49 : ((-118318975899/2500000000000 : ℚ) : ℝ) ≤ stT174 49 := by
  have hc : ((-331293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118318975899/2500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-331293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c50 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-18033/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 502147/1250000) (δ := 4413/500000000) (ψ := 501127/1000000) 174 108
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t50 : ((-6384469103/1250000000000 : ℚ) : ℝ) ≤ stT174 50 := by
  have hc : ((-9029/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6384469103/1250000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-9029/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c51 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((333613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -192291/625000) (δ := 8719/1000000000) (ψ := 501127/1000000) 174 109
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t51 : ((11677039941/250000000000 : ℚ) : ℝ) ≤ stT174 51 := by
  have hc : ((333563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11677039941/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((333563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c52 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-136439/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2685109/5000000) (δ := 2221/250000000) (ψ := 501127/1000000) 174 109
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t52 : ((-378448508153/5000000000000 : ℚ) : ℝ) ≤ stT174 52 := by
  have hc : ((-272903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-378448508153/5000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-272903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c53 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((681701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2051779/10000000) (δ := 2203/250000000) (ψ := 501127/1000000) 174 110
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t53 : ((187263844371/2000000000000 : ℚ) : ℝ) ≤ stT174 53 := by
  have hc : ((681651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187263844371/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((681651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c54 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-758441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1215857/2000000) (δ := 8791/1000000000) (ψ := 501127/1000000) 174 110
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t54 : ((-258043947637/2500000000000 : ℚ) : ℝ) ≤ stT174 54 := by
  have hc : ((-758491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258043947637/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-758491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c55 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((790771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -82341/500000) (δ := 1741/200000000) (ψ := 501127/1000000) 174 111
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t55 : ((1066207405679/10000000000000 : ℚ) : ℝ) ≤ stT174 55 := by
  have hc : ((790721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1066207405679/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((790721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c56 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-393427/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1547807/2500000) (δ := 4449/500000000) (ψ := 501127/1000000) 174 111
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t56 : ((-131443165441/1250000000000 : ℚ) : ℝ) ≤ stT174 56 := by
  have hc : ((-98363/125000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131443165441/1250000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-98363/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c57 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((186799/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -181741/1000000) (δ := 8797/1000000000) (ψ := 501127/1000000) 174 112
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t57 : ((123702348209/1250000000000 : ℚ) : ℝ) ≤ stT174 57 := by
  have hc : ((373573/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123702348209/1250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((373573/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c58 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-332843/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5748023/10000000) (δ := 8797/1000000000) (ψ := 501127/1000000) 174 112
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t58 : ((-21853866021/250000000000 : ℚ) : ℝ) ≤ stT174 58 := by
  have hc : ((-83217/125000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21853866021/250000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-83217/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c59 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((532241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -630969/2500000) (δ := 8713/1000000000) (ψ := 501127/1000000) 174 113
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t59 : ((692853608799/10000000000000 : ℚ) : ℝ) ≤ stT174 59 := by
  have hc : ((532191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((692853608799/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((532191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c60 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-337339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1196803/2500000) (δ := 889/100000000) (ψ := 501127/1000000) 174 113
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t60 : ((-87113502411/2000000000000 : ℚ) : ℝ) ≤ stT174 60 := by
  have hc : ((-337389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87113502411/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-337389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c61 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((78513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -746101/2000000) (δ := 441/50000000) (ψ := 501127/1000000) 174 114
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t61 : ((6278844649/625000000000 : ℚ) : ℝ) ≤ stT174 61 := by
  have hc : ((78463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6278844649/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((78463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c62 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((231551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 835703/2500000) (δ := 8783/1000000000) (ψ := 501127/1000000) 174 114
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t62 : ((294006501501/10000000000000 : ℚ) : ℝ) ≤ stT174 62 := by
  have hc : ((231501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((294006501501/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((231501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c63 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-557353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5404977/10000000) (δ := 8727/1000000000) (ψ := 501127/1000000) 174 115
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t63 : ((-351131003223/5000000000000 : ℚ) : ℝ) ≤ stT174 63 := by
  have hc : ((-557403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-351131003223/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-557403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c64 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((837441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1445533/10000000) (δ := 2219/250000000) (ψ := 501127/1000000) 174 115
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t64 : ((837391/8000000 : ℚ) : ℝ) ≤ stT174 64 := by
  have hc : ((837391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((837391/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((837391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c65 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-247747/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7518103/10000000) (δ := 8769/1000000000) (ψ := 501127/1000000) 174 116
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t65 : ((-153654000153/1250000000000 : ℚ) : ℝ) ≤ stT174 65 := by
  have hc : ((-495519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153654000153/1250000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-495519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c66 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((469567/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43837/500000) (δ := 4417/500000000) (ψ := 501127/1000000) 174 116
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t66 : ((144491455347/1250000000000 : ℚ) : ℝ) ≤ stT174 66 := by
  have hc : ((234771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144491455347/1250000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((234771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c67 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-40029/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2832373/5000000) (δ := 8769/1000000000) (ψ := 501127/1000000) 174 116
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t67 : ((-78251275123/1000000000000 : ℚ) : ℝ) ≤ stT174 67 := by
  have hc : ((-320257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78251275123/1000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-320257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c68 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((130959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3598649/10000000) (δ := 8861/1000000000) (ψ := 501127/1000000) 174 117
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t68 : ((79375232151/5000000000000 : ℚ) : ℝ) ≤ stT174 68 := by
  have hc : ((130909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79375232151/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((130909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c69 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((28309/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2751829/10000000) (δ := 8861/1000000000) (ψ := 501127/1000000) 174 117
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t69 : ((136305016263/2500000000000 : ℚ) : ℝ) ≤ stT174 69 := by
  have hc : ((226447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136305016263/2500000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((226447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c70 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-447409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6697049/10000000) (δ := 8849/1000000000) (ψ := 501127/1000000) 174 118
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t70 : ((-267393046193/2500000000000 : ℚ) : ℝ) ≤ stT174 70 := by
  have hc : ((-223717/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-267393046193/2500000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-223717/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c71 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((195577/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -131687/2500000) (δ := 8849/1000000000) (ψ := 501127/1000000) 174 118
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t71 : ((232095199827/2000000000000 : ℚ) : ℝ) ≤ stT174 71 := by
  have hc : ((195567/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((232095199827/2000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((195567/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c72 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-606873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1389323/2500000) (δ := 4377/500000000) (ψ := 501127/1000000) 174 118
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t72 : ((-44704127411/625000000000 : ℚ) : ℝ) ≤ stT174 72 := by
  have hc : ((-606923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44704127411/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-606923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c73 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-89319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2075293/5000000) (δ := 8847/1000000000) (ψ := 501127/1000000) 174 119
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t73 : ((-26149637507/2500000000000 : ℚ) : ℝ) ≤ stT174 73 := by
  have hc : ((-89369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26149637507/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-89369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c74 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((760223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 35357/200000) (δ := 8847/1000000000) (ψ := 501127/1000000) 174 119
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t74 : ((220920717087/2500000000000 : ℚ) : ℝ) ≤ stT174 74 := by
  have hc : ((760173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220920717087/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((760173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c75 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-12439/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7606899/10000000) (δ := 2189/250000000) (ψ := 501127/1000000) 174 119
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t75 : ((-114912379417/1000000000000 : ℚ) : ℝ) ≤ stT174 75 := by
  have hc : ((-99517/100000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114912379417/1000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-99517/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c76 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((296603/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1169701/5000000) (δ := 8863/1000000000) (ψ := 501127/1000000) 174 120
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t76 : ((85049524771/1250000000000 : ℚ) : ℝ) ≤ stT174 76 := by
  have hc : ((148289/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85049524771/1250000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((148289/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c77 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((14371/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3346961/10000000) (δ := 437/50000000) (ψ := 501127/1000000) 174 120
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t77 : ((26197923503/1000000000000 : ℚ) : ℝ) ≤ stT174 77 := by
  have hc : ((114943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26197923503/1000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((114943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c78 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-451867/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6748023/10000000) (δ := 877/100000000) (ψ := 501127/1000000) 174 121
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t78 : ((-63958421247/625000000000 : ℚ) : ℝ) ≤ stT174 78 := by
  have hc : ((-112973/125000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63958421247/625000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-112973/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c79 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((885781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -603279/5000000) (δ := 877/100000000) (ψ := 501127/1000000) 174 121
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t79 : ((996524433597/10000000000000 : ℚ) : ℝ) ≤ stT174 79 := by
  have hc : ((885731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((996524433597/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((885731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c80 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-134879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 213261/500000) (δ := 877/100000000) (ψ := 501127/1000000) 174 121
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t80 : ((-75427604793/5000000000000 : ℚ) : ℝ) ≤ stT174 80 := by
  have hc : ((-134929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75427604793/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-134929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c81 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-747829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1509739/2500000) (δ := 4363/500000000) (ψ := 501127/1000000) 174 122
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t81 : ((-103872166431/1250000000000 : ℚ) : ℝ) ≤ stT174 81 := by
  have hc : ((-747879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103872166431/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-747879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c82 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((480447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -350731/5000000) (δ := 8877/1000000000) (ψ := 501127/1000000) 174 122
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t82 : ((53053722093/500000000000 : ℚ) : ℝ) ≤ stT174 82 := by
  have hc : ((240211/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53053722093/500000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((240211/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c83 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-127449/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4571347/10000000) (δ := 8877/1000000000) (ψ := 501127/1000000) 174 122
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t83 : ((-69960471891/2500000000000 : ℚ) : ℝ) ≤ stT174 83 := by
  have hc : ((-63737/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69960471891/2500000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-63737/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c84 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-179339/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5926991/10000000) (δ := 3517/200000000) (ψ := 501127/1000000) 174 123
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t84 : ((-39137725627/500000000000 : ℚ) : ℝ) ≤ stT174 84 := by
  have hc : ((-358703/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39137725627/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-358703/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c85 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((237961/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -389503/5000000) (δ := 4409/500000000) (ψ := 501127/1000000) 174 123
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t85 : ((129045658211/1250000000000 : ℚ) : ℝ) ≤ stT174 85 := by
  have hc : ((475897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129045658211/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((475897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c86 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-9507/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2154377/5000000) (δ := 4409/500000000) (ψ := 501127/1000000) 174 123
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t86 : ((-10255034071/625000000000 : ℚ) : ℝ) ≤ stT174 86 := by
  have hc : ((-76081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10255034071/625000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-76081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c87 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-165797/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6370217/10000000) (δ := 2223/250000000) (ψ := 501127/1000000) 174 124
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t87 : ((-177763840191/2000000000000 : ℚ) : ℝ) ≤ stT174 87 := by
  have hc : ((-165807/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177763840191/2000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-165807/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c88 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((211881/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1398733/10000000) (δ := 8711/1000000000) (ψ := 501127/1000000) 174 124
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t88 : ((451704913211/5000000000000 : ℚ) : ℝ) ≤ stT174 88 := by
  have hc : ((423737/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((451704913211/5000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((423737/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c89 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((2043/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 70331/200000) (δ := 2223/250000000) (ψ := 501127/1000000) 174 124
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t89 : ((17319290983/1000000000000 : ℚ) : ℝ) ≤ stT174 89 := by
  have hc : ((16339/100000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17319290983/1000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((16339/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c90 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-978201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1832757/2500000) (δ := 8799/1000000000) (ψ := 501127/1000000) 174 125
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t90 : ((-1031167531343/10000000000000 : ℚ) : ℝ) ≤ stT174 90 := by
  have hc : ((-978251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1031167531343/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-978251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c91 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((532083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2524343/10000000) (δ := 17599/1000000000) (ψ := 501127/1000000) 174 125
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t91 : ((139430420343/2500000000000 : ℚ) : ℝ) ≤ stT174 91 := by
  have hc : ((532033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139430420343/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((532033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c92 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((627921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2229793/10000000) (δ := 2201/250000000) (ψ := 501127/1000000) 174 125
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t92 : ((163650181053/2500000000000 : ℚ) : ℝ) ≤ stT174 92 := by
  have hc : ((627871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163650181053/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((627871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c93 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-23321/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1386507/2000000) (δ := 8799/1000000000) (ψ := 501127/1000000) 174 125
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t93 : ((-12092026891/125000000000 : ℚ) : ℝ) ≤ stT174 93 := by
  have hc : ((-93289/100000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12092026891/125000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-93289/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c94 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-78313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4122973/10000000) (δ := 4353/500000000) (ψ := 501127/1000000) 174 126
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t94 : ((-40412661093/5000000000000 : ℚ) : ℝ) ≤ stT174 94 := by
  have hc : ((-78363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40412661093/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-78363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c95 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((490803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6003/125000) (δ := 8897/1000000000) (ψ := 501127/1000000) 174 126
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t95 : ((125881857721/1250000000000 : ℚ) : ℝ) ≤ stT174 95 := by
  have hc : ((245389/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125881857721/1250000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((245389/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c96 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-6702/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 629407/1250000) (δ := 4353/500000000) (ψ := 501127/1000000) 174 126
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t96 : ((-218911977669/5000000000000 : ℚ) : ℝ) ≤ stT174 96 := by
  have hc : ((-214489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218911977669/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-214489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c97 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-780309/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6164889/10000000) (δ := 8813/1000000000) (ψ := 501127/1000000) 174 127
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t97 : ((-792335169573/10000000000000 : ℚ) : ℝ) ≤ stT174 97 := by
  have hc : ((-780359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-792335169573/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-780359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c98 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((776739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -106457/625000) (δ := 879/100000000) (ψ := 501127/1000000) 174 127
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t98 : ((98071743341/1250000000000 : ℚ) : ℝ) ≤ stT174 98 := by
  have hc : ((776689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98071743341/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((776689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c99 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((233371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1356491/5000000) (δ := 879/100000000) (ψ := 501127/1000000) 174 127
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t99 : ((117260681901/2500000000000 : ℚ) : ℝ) ≤ stT174 99 := by
  have hc : ((116673/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117260681901/2500000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((116673/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c100 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-953049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7084863/10000000) (δ := 8813/1000000000) (ψ := 501127/1000000) 174 127
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t100 : ((-953099/10000000 : ℚ) : ℝ) ≤ stT174 100 := by
  have hc : ((-953099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-953099/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-953099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c101 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-29309/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4294677/10000000) (δ := 8883/1000000000) (ψ := 501127/1000000) 174 128
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t101 : ((-14586759561/1000000000000 : ℚ) : ℝ) ≤ stT174 101 := by
  have hc : ((-29319/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14586759561/1000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-29319/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c102 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((499997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4463/5000000) (δ := 109/12500000) (ψ := 501127/1000000) 174 128
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t102 : ((123761443971/1250000000000 : ℚ) : ℝ) ≤ stT174 102 := by
  have hc : ((124993/125000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123761443971/1250000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((124993/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c103 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-122883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4234977/10000000) (δ := 8883/1000000000) (ψ := 501127/1000000) 174 128
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t103 : ((-12112957289/1000000000000 : ℚ) : ℝ) ≤ stT174 103 := by
  have hc : ((-122933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12112957289/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-122933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c104 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-972847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7270059/10000000) (δ := 2207/250000000) (ψ := 501127/1000000) 174 129
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t104 : ((-954004313157/10000000000000 : ℚ) : ℝ) ≤ stT174 104 := by
  have hc : ((-972897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-954004313157/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-972897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c105 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((322023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3107327/10000000) (δ := 351/40000000) (ψ := 501127/1000000) 174 129
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t105 : ((3142134507/100000000000 : ℚ) : ℝ) ≤ stT174 105 := by
  have hc : ((321973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3142134507/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((321973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c106 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((229641/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 253977/2500000) (δ := 2207/250000000) (ψ := 501127/1000000) 174 129
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t106 : ((89213887049/1000000000000 : ℚ) : ℝ) ≤ stT174 106 := by
  have hc : ((459257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89213887049/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((459257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c107 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-56543/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5100471/10000000) (δ := 2207/250000000) (ψ := 501127/1000000) 174 129
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t107 : ((-218673009189/5000000000000 : ℚ) : ℝ) ≤ stT174 107 := by
  have hc : ((-226197/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218673009189/5000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-226197/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c108 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-869201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6560949/10000000) (δ := 2217/250000000) (ψ := 501127/1000000) 174 130
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t108 : ((-836437644001/10000000000000 : ℚ) : ℝ) ≤ stT174 108 := by
  have hc : ((-869251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-836437644001/10000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-869251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c109 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((522777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -159483/625000) (δ := 2217/250000000) (ψ := 501127/1000000) 174 130
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t109 : ((250340755751/5000000000000 : ℚ) : ℝ) ≤ stT174 109 := by
  have hc : ((522727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250340755751/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((522727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c110 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((842783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 142091/1000000) (δ := 1747/200000000) (ψ := 501127/1000000) 174 130
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t110 : ((401756945823/5000000000000 : ℚ) : ℝ) ≤ stT174 110 := by
  have hc : ((842733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((401756945823/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((842733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c111 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-21661/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 334851/625000) (δ := 2217/250000000) (ψ := 501127/1000000) 174 130
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t111 : ((-10280804877/200000000000 : ℚ) : ℝ) ≤ stT174 111 := by
  have hc : ((-21663/40000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10280804877/200000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-21663/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c112 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-211549/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3224503/5000000) (δ := 8761/1000000000) (ψ := 501127/1000000) 174 131
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t112 : ((-24988375011/312500000000 : ℚ) : ℝ) ≤ stT174 112 := by
  have hc : ((-423123/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24988375011/312500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-423123/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c113 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((128079/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2582291/10000000) (δ := 8761/1000000000) (ψ := 501127/1000000) 174 131
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t113 : ((3011867947/62500000000 : ℚ) : ℝ) ≤ stT174 113 := by
  have hc : ((256133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3011867947/62500000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((256133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c114 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((877521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15629/125000) (δ := 8761/1000000000) (ψ := 501127/1000000) 174 131
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t114 : ((164365235307/2000000000000 : ℚ) : ℝ) ≤ stT174 114 := by
  have hc : ((877471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164365235307/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((877471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c115 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-434061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126237/250000) (δ := 4421/500000000) (ψ := 501127/1000000) 174 131
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t115 : ((-80962135611/2000000000000 : ℚ) : ℝ) ≤ stT174 115 := by
  have hc : ((-434111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80962135611/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-434111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c116 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-463457/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3446127/5000000) (δ := 4427/500000000) (ψ := 501127/1000000) 174 132
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t116 : ((-215166188457/2500000000000 : ℚ) : ℝ) ≤ stT174 116 := by
  have hc : ((-231741/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215166188457/2500000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-231741/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c117 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((151327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3158301/10000000) (δ := 4427/500000000) (ψ := 501127/1000000) 174 132
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t117 : ((139878699/5000000000 : ℚ) : ℝ) ≤ stT174 117 := by
  have hc : ((75651/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139878699/5000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((75651/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c118 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((976431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 271927/5000000) (δ := 8749/1000000000) (ψ := 501127/1000000) 174 132
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t118 : ((449415481347/5000000000000 : ℚ) : ℝ) ≤ stT174 118 := by
  have hc : ((976381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((449415481347/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((976381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c119 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-114843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1053683/2500000) (δ := 8749/1000000000) (ψ := 501127/1000000) 174 132
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t119 : ((-105322298207/10000000000000 : ℚ) : ℝ) ≤ stT174 119 := by
  have hc : ((-114893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105322298207/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-114893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c120 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7853021/10000000) (δ := 8747/1000000000) (ψ := 501127/1000000) 174 133
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t120 : ((-18258332871/200000000000 : ℚ) : ℝ) ≤ stT174 120 := by
  have hc : ((-20001/20000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18258332871/200000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-20001/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c121 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-31521/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4243043/10000000) (δ := 8747/1000000000) (ψ := 501127/1000000) 174 133
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t121 : ((-57333642097/5000000000000 : ℚ) : ℝ) ≤ stT174 121 := by
  have hc : ((-63067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57333642097/5000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-63067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c122 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((120633/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -26511/400000) (δ := 1107/125000000) (ψ := 501127/1000000) 174 133
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t122 : ((436841089999/5000000000000 : ℚ) : ℝ) ≤ stT174 122 := by
  have hc : ((482507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((436841089999/5000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((482507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c123 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((10091/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 144413/500000) (δ := 8747/1000000000) (ψ := 501127/1000000) 174 133
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t123 : ((36390459171/1000000000000 : ℚ) : ℝ) ≤ stT174 123 := by
  have hc : ((40359/100000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36390459171/1000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((40359/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c124 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-418949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3205271/5000000) (δ := 8747/1000000000) (ψ := 501127/1000000) 174 133
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t124 : ((-188124982149/2500000000000 : ℚ) : ℝ) ≤ stT174 124 := by
  have hc : ((-209487/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188124982149/2500000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-209487/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c125 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-136411/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2901707/5000000) (δ := 2191/250000000) (ψ := 501127/1000000) 174 134
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t125 : ((-30504690547/500000000000 : ℚ) : ℝ) ≤ stT174 125 := by
  have hc : ((-136421/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30504690547/500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-136421/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c126 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((5939/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2337247/10000000) (δ := 2191/250000000) (ψ := 501127/1000000) 174 134
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t126 : ((1058086299/20000000000 : ℚ) : ℝ) ≤ stT174 126 := by
  have hc : ((11877/20000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1058086299/20000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((11877/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c127 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((904501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1101471/10000000) (δ := 8839/1000000000) (ψ := 501127/1000000) 174 134
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t127 : ((200642505389/2500000000000 : ℚ) : ℝ) ≤ stT174 127 := by
  have hc : ((904451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200642505389/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((904451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c128 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-46473/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4513263/10000000) (δ := 8839/1000000000) (ψ := 501127/1000000) 174 134
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t128 : ((-10271394993/500000000000 : ℚ) : ℝ) ≤ stT174 128 := by
  have hc : ((-46483/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10271394993/500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-46483/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c129 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-999841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7809443/10000000) (δ := 2183/250000000) (ψ := 501127/1000000) 174 135
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t129 : ((-880355030841/10000000000000 : ℚ) : ℝ) ≤ stT174 129 := by
  have hc : ((-999891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-880355030841/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-999891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c130 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-207827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4450373/10000000) (δ := 2183/250000000) (ψ := 501127/1000000) 174 135
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t130 : ((-182320393743/10000000000000 : ℚ) : ℝ) ≤ stT174 130 := by
  have hc : ((-207877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182320393743/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-207877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c131 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((112729/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1117011/10000000) (δ := 8871/1000000000) (ψ := 501127/1000000) 174 135
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t131 : ((49243158783/625000000000 : ℚ) : ℝ) ≤ stT174 131 := by
  have hc : ((450891/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49243158783/625000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((450891/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c132 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((25597/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 219099/1000000) (δ := 8871/1000000000) (ψ := 501127/1000000) 174 135
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t132 : ((1113879043/20000000000 : ℚ) : ℝ) ≤ stT174 132 := by
  have hc : ((5119/8000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1113879043/20000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((5119/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c133 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-145017/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2737011/5000000) (δ := 8871/1000000000) (ψ := 501127/1000000) 174 135
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t133 : ((-25151305949/500000000000 : ℚ) : ℝ) ≤ stT174 133 := by
  have hc : ((-290059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25151305949/500000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-290059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c134 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-58681/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6975509/10000000) (δ := 697/40000000) (ψ := 501127/1000000) 174 136
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t134 : ((-405563171037/5000000000000 : ℚ) : ℝ) ≤ stT174 134 := by
  have hc : ((-469473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-405563171037/5000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-469473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c135 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((37103/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1870653/5000000) (δ := 353/40000000) (ψ := 501127/1000000) 174 136
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t135 : ((7977906409/1250000000000 : ℚ) : ℝ) ≤ stT174 135 := by
  have hc : ((18539/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7977906409/1250000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((18539/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c136 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((977531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -265481/5000000) (δ := 4389/500000000) (ψ := 501127/1000000) 174 136
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t136 : ((209545534413/2500000000000 : ℚ) : ℝ) ≤ stT174 136 := by
  have hc : ((977481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209545534413/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((977481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c137 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((97363/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2655891/10000000) (δ := 353/40000000) (ψ := 501127/1000000) 174 136
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t137 : ((83174217021/2000000000000 : ℚ) : ℝ) ≤ stT174 137 := by
  have hc : ((97353/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83174217021/2000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((97353/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c138 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-686751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1454879/2500000) (δ := 4389/500000000) (ψ := 501127/1000000) 174 136
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t138 : ((-584644158857/10000000000000 : ℚ) : ℝ) ≤ stT174 138 := by
  have hc : ((-686801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-584644158857/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-686801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c139 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-56479/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6747617/10000000) (δ := 4359/500000000) (ψ := 501127/1000000) 174 137
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t139 : ((-383260136973/5000000000000 : ℚ) : ℝ) ≤ stT174 139 := by
  have hc : ((-451857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-383260136973/5000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-451857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c140 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((29697/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3629319/10000000) (δ := 1777/200000000) (ψ := 501127/1000000) 174 137
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t140 : ((25087973913/2500000000000 : ℚ) : ℝ) ≤ stT174 140 := by
  have hc : ((59369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25087973913/2500000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((59369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c141 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((488669/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2133/40000) (δ := 1777/200000000) (ψ := 501127/1000000) 174 137
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t141 : ((102878008311/1250000000000 : ℚ) : ℝ) ≤ stT174 141 := by
  have hc : ((122161/125000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102878008311/1250000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((122161/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c142 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((131609/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1270491/5000000) (δ := 1777/200000000) (ψ := 501127/1000000) 174 137
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t142 : ((220866564933/5000000000000 : ℚ) : ℝ) ≤ stT174 142 := by
  have hc : ((263193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220866564933/5000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((263193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c143 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-154591/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2796819/5000000) (δ := 1777/200000000) (ψ := 501127/1000000) 174 137
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t143 : ((-258572189301/5000000000000 : ℚ) : ℝ) ≤ stT174 143 := by
  have hc : ((-309207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258572189301/5000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-309207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c144 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-952821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1416597/2000000) (δ := 8811/1000000000) (ψ := 501127/1000000) 174 138
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t144 : ((-397029900957/5000000000000 : ℚ) : ℝ) ≤ stT174 144 := by
  have hc : ((-952871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-397029900957/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-952871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c145 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-29099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4072567/10000000) (δ := 1099/125000000) (ψ := 501127/1000000) 174 138
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t145 : ((-1209308571/250000000000 : ℚ) : ℝ) ≤ stT174 145 := by
  have hc : ((-7281/125000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1209308571/250000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-7281/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c146 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((907651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -135357/1250000) (δ := 8811/1000000000) (ψ := 501127/1000000) 174 138
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t146 : ((150227025121/2000000000000 : ℚ) : ℝ) ≤ stT174 146 := by
  have hc : ((907601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150227025121/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((907601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c147 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((72857/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1886411/10000000) (δ := 1099/125000000) (ψ := 501127/1000000) 174 138
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t147 : ((7510913709/125000000000 : ℚ) : ℝ) ≤ stT174 147 := by
  have hc : ((18213/25000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7510913709/125000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((18213/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c148 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-11109/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 241779/500000) (δ := 8811/1000000000) (ψ := 501127/1000000) 174 138
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t148 : ((-29225045831/1000000000000 : ℚ) : ℝ) ≤ stT174 148 := by
  have hc : ((-177769/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29225045831/1000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-177769/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c149 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-199873/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3882457/5000000) (δ := 1099/125000000) (ψ := 501127/1000000) 174 138
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t149 : ((-5117204683/62500000000 : ℚ) : ℝ) ≤ stT174 149 := by
  have hc : ((-199883/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5117204683/62500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-199883/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c150 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-1713/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2516689/5000000) (δ := 17/1953125) (ψ := 501127/1000000) 174 139
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t150 : ((-3497056651/100000000000 : ℚ) : ℝ) ≤ stT174 150 := by
  have hc : ((-4283/10000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3497056651/100000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-4283/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c151 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((163641/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2142977/10000000) (δ := 17/1953125) (ψ := 501127/1000000) 174 139
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t151 : ((66579454879/1250000000000 : ℚ) : ℝ) ≤ stT174 151 := by
  have hc : ((327257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66579454879/1250000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((327257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c152 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((478931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 91041/1250000) (δ := 8899/1000000000) (ψ := 501127/1000000) 174 139
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t152 : ((194222004471/2500000000000 : ℚ) : ℝ) ≤ stT174 152 := by
  have hc : ((239453/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194222004471/2500000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((239453/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c153 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((27607/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3580797/10000000) (δ := 8899/1000000000) (ψ := 501127/1000000) 174 139
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t153 : ((5577712461/500000000000 : ℚ) : ℝ) ≤ stT174 153 := by
  have hc : ((27597/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5577712461/500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((27597/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c154 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-838803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6414691/10000000) (δ := 17/1953125) (ψ := 501127/1000000) 174 139
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t154 : ((-675967041019/10000000000000 : ℚ) : ℝ) ≤ stT174 154 := by
  have hc : ((-838853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-675967041019/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-838853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c155 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-106533/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1295547/2000000) (δ := 2199/250000000) (ψ := 501127/1000000) 174 140
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t155 : ((-17114891277/250000000000 : ℚ) : ℝ) ≤ stT174 155 := by
  have hc : ((-426157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17114891277/250000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-426157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c156 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((98519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3680293/10000000) (δ := 8807/1000000000) (ψ := 501127/1000000) 174 140
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t156 : ((123184719/15625000000 : ℚ) : ℝ) ≤ stT174 156 := by
  have hc : ((98469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123184719/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((98469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c157 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((467897/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -90073/1000000) (δ := 8807/1000000000) (ψ := 501127/1000000) 174 140
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t157 : ((5834407703/78125000000 : ℚ) : ℝ) ≤ stT174 157 := by
  have hc : ((14621/15625 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5834407703/78125000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((14621/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c158 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((91931/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 465293/2500000) (δ := 8807/1000000000) (ψ := 501127/1000000) 174 140
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t158 : ((292525513343/5000000000000 : ℚ) : ℝ) ≤ stT174 158 := by
  have hc : ((367699/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((292525513343/5000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((367699/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c159 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-268151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2302837/5000000) (δ := 8807/1000000000) (ψ := 501127/1000000) 174 140
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t159 : ((-53174334863/2500000000000 : ℚ) : ℝ) ≤ stT174 159 := by
  have hc : ((-268201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53174334863/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-268201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c160 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-978361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 146659/200000) (δ := 8807/1000000000) (ψ := 501127/1000000) 174 140
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t160 : ((-77350238427/1000000000000 : ℚ) : ℝ) ≤ stT174 160 := by
  have hc : ((-978411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77350238427/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-978411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c161 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-40029/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2832373/5000000) (δ := 4357/500000000) (ψ := 501127/1000000) 174 141
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t161 : ((-252398064527/5000000000000 : ℚ) : ℝ) ≤ stT174 161 := by
  have hc : ((-320257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252398064527/5000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-320257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c162 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((373061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1485613/5000000) (δ := 4357/500000000) (ψ := 501127/1000000) 174 141
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t162 : ((146532522207/5000000000000 : ℚ) : ℝ) ≤ stT174 162 := by
  have hc : ((373011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146532522207/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((373011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c163 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((24827/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7357/250000) (δ := 8889/1000000000) (ψ := 501127/1000000) 174 141
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t163 : ((3889003389/50000000000 : ℚ) : ℝ) ≤ stT174 163 := by
  have hc : ((99303/100000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3889003389/50000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((99303/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c164 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((584521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2366267/10000000) (δ := 8889/1000000000) (ψ := 501127/1000000) 174 141
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t164 : ((114098675207/2500000000000 : ℚ) : ℝ) ≤ stT174 164 := by
  have hc : ((584471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114098675207/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((584471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c165 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-42001/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 626329/1250000) (δ := 8889/1000000000) (ψ := 501127/1000000) 174 141
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t165 : ((-16350814497/500000000000 : ℚ) : ℝ) ≤ stT174 165 := by
  have hc : ((-21003/50000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16350814497/500000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-21003/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c166 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-498153/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7639033/10000000) (δ := 4357/500000000) (ψ := 501127/1000000) 174 141
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t166 : ((-193330676439/2500000000000 : ℚ) : ℝ) ≤ stT174 166 := by
  have hc : ((-249089/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193330676439/2500000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-249089/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c167 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-8973/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5456277/10000000) (δ := 4391/500000000) (ψ := 501127/1000000) 174 142
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t167 : ((-3472063651/78125000000 : ℚ) : ℝ) ≤ stT174 167 := by
  have hc : ((-287161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3472063651/78125000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-287161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c168 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((207109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2859283/10000000) (δ := 8821/1000000000) (ψ := 501127/1000000) 174 142
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t168 : ((9985538709/312500000000 : ℚ) : ℝ) ≤ stT174 168 := by
  have hc : ((51771/125000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9985538709/312500000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((51771/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c169 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((993839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55529/2000000) (δ := 8821/1000000000) (ψ := 501127/1000000) 174 142
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t169 : ((76445231247/1000000000000 : ℚ) : ℝ) ≤ stT174 169 := by
  have hc : ((993789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76445231247/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((993789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c170 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((304701/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 572181/2500000) (δ := 4391/500000000) (ψ := 501127/1000000) 174 142
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t170 : ((14604720229/312500000000 : ℚ) : ℝ) ≤ stT174 170 := by
  have hc : ((76169/125000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14604720229/312500000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((76169/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c171 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-89289/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4840043/10000000) (δ := 8821/1000000000) (ψ := 501127/1000000) 174 142
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t171 : ((-1707266077/62500000000 : ℚ) : ℝ) ≤ stT174 171 := by
  have hc : ((-178603/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1707266077/62500000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-178603/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c172 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-196363/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1844121/2500000) (δ := 4391/500000000) (ψ := 501127/1000000) 174 142
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t172 : ((-149733037889/2000000000000 : ℚ) : ℝ) ≤ stT174 172 := by
  have hc : ((-196373/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149733037889/2000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-196373/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c173 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-10686/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5809741/10000000) (δ := 71/8000000) (ψ := 501127/1000000) 174 143
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t173 : ((-130000162711/2500000000000 : ℚ) : ℝ) ≤ stT174 173 := by
  have hc : ((-341977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130000162711/2500000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-341977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c174 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((49439/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3302531/10000000) (δ := 1091/125000000) (ψ := 501127/1000000) 174 143
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t174 : ((18736013021/1000000000000 : ℚ) : ℝ) ≤ stT174 174 := by
  have hc : ((49429/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18736013021/1000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((49429/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c175 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((948011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -809677/10000000) (δ := 71/8000000) (ψ := 501127/1000000) 174 143
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t175 : ((89573782851/1250000000000 : ℚ) : ℝ) ≤ stT174 175 := by
  have hc : ((947961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89573782851/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((947961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c176 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((785321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1668953/10000000) (δ := 71/8000000) (ψ := 501127/1000000) 174 143
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t176 : ((295960001919/5000000000000 : ℚ) : ℝ) ≤ stT174 176 := by
  have hc : ((785271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((295960001919/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((785271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c177 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-4127/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 516697/1250000) (δ := 71/8000000) (ψ := 501127/1000000) 174 143
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t177 : ((-6207852573/1000000000000 : ℚ) : ℝ) ≤ stT174 177 := by
  have hc : ((-8259/100000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6207852573/1000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-8259/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c178 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-873777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6584279/10000000) (δ := 71/8000000) (ψ := 501127/1000000) 174 143
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t178 : ((-163740324741/2500000000000 : ℚ) : ℝ) ≤ stT174 178 := by
  have hc : ((-873827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163740324741/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-873827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c179 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-892959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6686683/10000000) (δ := 1767/200000000) (ψ := 501127/1000000) 174 144
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t179 : ((-166866768731/2500000000000 : ℚ) : ℝ) ≤ stT174 179 := by
  have hc : ((-893009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166866768731/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-893009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c180 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-67059/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2131649/5000000) (δ := 1767/200000000) (ψ := 501127/1000000) 174 144
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t180 : ((-3125091369/312500000000 : ℚ) : ℝ) ≤ stT174 180 := by
  have hc : ((-16771/125000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3125091369/312500000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-16771/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c181 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((29503/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1853311/10000000) (δ := 1767/200000000) (ψ := 501127/1000000) 174 144
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t181 : ((10963958147/200000000000 : ℚ) : ℝ) ≤ stT174 181 := by
  have hc : ((29501/40000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10963958147/200000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((29501/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c182 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((976473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 108673/2000000) (δ := 1767/200000000) (ψ := 501127/1000000) 174 144
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t182 : ((723772572327/10000000000000 : ℚ) : ℝ) ≤ stT174 182 := by
  have hc : ((976423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((723772572327/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((976423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c183 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((194717/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2926947/10000000) (δ := 137/15625000) (ψ := 501127/1000000) 174 144
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t183 : ((35980103733/1250000000000 : ℚ) : ℝ) ≤ stT174 183 := by
  have hc : ((48673/125000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35980103733/1250000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((48673/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c184 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-521163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5297523/10000000) (δ := 137/15625000) (ψ := 501127/1000000) 174 144
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t184 : ((-38424343573/1000000000000 : ℚ) : ℝ) ≤ stT174 184 := by
  have hc : ((-521213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38424343573/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-521213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c185 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-996843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7655267/10000000) (δ := 1767/200000000) (ψ := 501127/1000000) 174 144
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t185 : ((-146586137399/2000000000000 : ℚ) : ℝ) ≤ stT174 185 := by
  have hc : ((-996893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146586137399/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-996893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c186 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-163391/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5707699/10000000) (δ := 443/50000000) (ψ := 501127/1000000) 174 145
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t186 : ((-59906664363/1250000000000 : ℚ) : ℝ) ≤ stT174 186 := by
  have hc : ((-326807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59906664363/1250000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-326807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c187 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((218917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3375229/10000000) (δ := 443/50000000) (ψ := 501127/1000000) 174 145
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t187 : ((20006413603/1250000000000 : ℚ) : ℝ) ≤ stT174 187 := by
  have hc : ((218867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20006413603/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((218867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c188 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((114029/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1055243/10000000) (δ := 8743/1000000000) (ψ := 501127/1000000) 174 145
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t188 : ((83159528121/1250000000000 : ℚ) : ℝ) ≤ stT174 188 := by
  have hc : ((456091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83159528121/1250000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((456091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c189 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((219277/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50099/400000) (δ := 443/50000000) (ψ := 501127/1000000) 174 145
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t189 : ((9968202699/156250000000 : ℚ) : ℝ) ≤ stT174 189 := by
  have hc : ((438529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9968202699/156250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((438529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c190 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((37757/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 354797/1000000) (δ := 443/50000000) (ψ := 501127/1000000) 174 145
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t190 : ((13691364441/1250000000000 : ℚ) : ℝ) ≤ stT174 190 := by
  have hc : ((75489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13691364441/1250000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((75489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c191 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-86277/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5831459/10000000) (δ := 443/50000000) (ψ := 501127/1000000) 174 145
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t191 : ((-9989184419/200000000000 : ℚ) : ℝ) ≤ stT174 191 := by
  have hc : ((-345133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9989184419/200000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-345133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c192 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-248761/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7604977/10000000) (δ := 177/20000000) (ψ := 501127/1000000) 174 146
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t192 : ((-44884212417/625000000000 : ℚ) : ℝ) ≤ stT174 192 := by
  have hc : ((-497547/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44884212417/625000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-497547/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c193 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-134339/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5345239/10000000) (δ := 177/20000000) (ψ := 501127/1000000) 174 146
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t193 : ((-24177089831/625000000000 : ℚ) : ℝ) ≤ stT174 193 := by
  have hc : ((-268703/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24177089831/625000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-268703/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c194 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((325871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3097159/10000000) (δ := 177/20000000) (ψ := 501127/1000000) 174 146
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t194 : ((116962896759/5000000000000 : ℚ) : ℝ) ≤ stT174 194 := by
  have hc : ((325821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116962896759/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((325821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c195 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((37653/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17213/200000) (δ := 177/20000000) (ψ := 501127/1000000) 174 146
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t195 : ((13481204107/200000000000 : ℚ) : ℝ) ≤ stT174 195 := by
  have hc : ((37651/40000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13481204107/200000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((37651/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c196 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((854729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 682209/5000000) (δ := 8753/1000000000) (ψ := 501127/1000000) 174 146
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t196 : ((122096877903/2000000000000 : ℚ) : ℝ) ≤ stT174 196 := by
  have hc : ((854679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122096877903/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((854679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c197 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((139073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3578177/10000000) (δ := 177/20000000) (ψ := 501127/1000000) 174 146
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t197 : ((9904971681/1000000000000 : ℚ) : ℝ) ≤ stT174 197 := by
  have hc : ((139023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9904971681/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((139023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c198 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-337693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 722589/1250000) (δ := 8753/1000000000) (ψ := 501127/1000000) 174 146
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t198 : ((-12000302553/250000000000 : ℚ) : ℝ) ≤ stT174 198 := by
  have hc : ((-168859/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12000302553/250000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-168859/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c199 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-998883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -60436/78125) (δ := 8757/1000000000) (ψ := 501127/1000000) 174 147
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t199 : ((-354062811453/5000000000000 : ℚ) : ℝ) ≤ stT174 199 := by
  have hc : ((-998933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-354062811453/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-998933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c200 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-303131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5555371/10000000) (δ := 4423/500000000) (ψ := 501127/1000000) 174 147
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t200 : ((-53590932423/1250000000000 : ℚ) : ℝ) ≤ stT174 200 := by
  have hc : ((-75789/125000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53590932423/1250000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-75789/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c201 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((214803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -677153/2000000) (δ := 4423/500000000) (ψ := 501127/1000000) 174 147
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t201 : ((30294990957/2000000000000 : ℚ) : ℝ) ≤ stT174 201 := by
  have hc : ((214753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30294990957/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((214753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c202 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((440979/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -122699/1000000) (δ := 8757/1000000000) (ψ := 501127/1000000) 174 147
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t202 : ((155126955769/2500000000000 : ℚ) : ℝ) ≤ stT174 202 := by
  have hc : ((220477/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155126955769/2500000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((220477/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c203 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((11661/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 92117/1000000) (δ := 4423/500000000) (ψ := 501127/1000000) 174 147
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t203 : ((32735896473/500000000000 : ℚ) : ℝ) ≤ stT174 203 := by
  have hc : ((93283/100000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32735896473/500000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((93283/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c204 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((340353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 76469/250000) (δ := 4423/500000000) (ψ := 501127/1000000) 174 147
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t204 : ((11912987121/500000000000 : ℚ) : ℝ) ≤ stT174 204 := by
  have hc : ((340303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11912987121/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((340303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c205 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-482553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 518591/1000000) (δ := 4423/500000000) (ψ := 501127/1000000) 174 147
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t205 : ((-337064895893/10000000000000 : ℚ) : ℝ) ≤ stT174 205 := by
  have hc : ((-482603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-337064895893/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-482603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c206 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-487893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7302707/10000000) (δ := 4423/500000000) (ψ := 501127/1000000) 174 147
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t206 : ((-84987264953/1250000000000 : ℚ) : ℝ) ≤ stT174 206 := by
  have hc : ((-243959/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84987264953/1250000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-243959/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c207 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-162531/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -251949/400000) (δ := 8739/1000000000) (ψ := 501127/1000000) 174 148
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t207 : ((-112973959509/2000000000000 : ℚ) : ℝ) ≤ stT174 207 := by
  have hc : ((-162541/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112973959509/2000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-162541/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c208 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-109913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4202329/10000000) (δ := 277/31250000) (ψ := 501127/1000000) 174 148
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t208 : ((-595669571/78125000000 : ℚ) : ℝ) ≤ stT174 208 := by
  have hc : ((-109963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-595669571/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-109963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c209 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((662689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1057991/5000000) (δ := 277/31250000) (ψ := 501127/1000000) 174 148
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t209 : ((229178336623/5000000000000 : ℚ) : ℝ) ≤ stT174 209 := by
  have hc : ((662639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229178336623/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((662639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c210 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((7999/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -39597/10000000) (δ := 8739/1000000000) (ψ := 501127/1000000) 174 148
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t210 : ((5519553909/80000000000 : ℚ) : ℝ) ≤ stT174 210 := by
  have hc : ((39993/40000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5519553909/80000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((39993/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c211 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((43059/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1013457/5000000) (δ := 8739/1000000000) (ψ := 501127/1000000) 174 148
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t211 : ((59281739829/1250000000000 : ℚ) : ℝ) ≤ stT174 211 := by
  have hc : ((344447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59281739829/1250000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((344447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c212 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-31309/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2041819/5000000) (δ := 277/31250000) (ψ := 501127/1000000) 174 148
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t212 : ((-10760142601/2500000000000 : ℚ) : ℝ) ≤ stT174 212 := by
  have hc : ((-15667/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10760142601/2500000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-15667/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c213 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-192921/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 383169/625000) (δ := 8739/1000000000) (ψ := 501127/1000000) 174 148
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t213 : ((-264391823863/5000000000000 : ℚ) : ℝ) ≤ stT174 213 := by
  have hc : ((-385867/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264391823863/5000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-385867/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c214 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-62007/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7539763/10000000) (δ := 69/7812500) (ψ := 501127/1000000) 174 149
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t214 : ((-169557013233/2500000000000 : ℚ) : ℝ) ≤ stT174 214 := by
  have hc : ((-496081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169557013233/2500000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-496081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c215 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-148077/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5511793/10000000) (δ := 69/7812500) (ψ := 501127/1000000) 174 149
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t215 : ((-40398519421/1000000000000 : ℚ) : ℝ) ≤ stT174 215 := by
  have hc : ((-296179/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40398519421/1000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-296179/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c216 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((172639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3493219/10000000) (δ := 69/7812500) (ψ := 501127/1000000) 174 149
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t216 : ((117431799257/10000000000000 : ℚ) : ℝ) ≤ stT174 216 := by
  have hc : ((172589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117431799257/10000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((172589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c217 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((828933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1483997/10000000) (δ := 8771/1000000000) (ψ := 501127/1000000) 174 149
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t217 : ((140670562813/2500000000000 : ℚ) : ℝ) ≤ stT174 217 := by
  have hc : ((828883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140670562813/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((828883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c218 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((39151/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 258001/5000000) (δ := 69/7812500) (ψ := 501127/1000000) 174 149
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t218 : ((5303006093/80000000000 : ℚ) : ℝ) ≤ stT174 218 := by
  have hc : ((39149/40000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5303006093/80000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((39149/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c219 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((537989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2506867/10000000) (δ := 8771/1000000000) (ψ := 501127/1000000) 174 149
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t219 : ((363505286043/10000000000000 : ℚ) : ℝ) ≤ stT174 219 := by
  have hc : ((537939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((363505286043/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((537939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c220 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-8911/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14027/31250) (δ := 8771/1000000000) (ψ := 501127/1000000) 174 149
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t220 : ((-30045723/2000000000 : ℚ) : ℝ) ≤ stT174 220 := by
  have hc : ((-8913/40000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30045723/2000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-8913/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c221 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-848839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1615363/2500000) (δ := 8771/1000000000) (ψ := 501127/1000000) 174 149
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t221 : ((-571024710297/10000000000000 : ℚ) : ℝ) ≤ stT174 221 := by
  have hc : ((-848889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-571024710297/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-848889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c222 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-974001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -364133/500000) (δ := 4439/500000000) (ψ := 501127/1000000) 174 150
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t222 : ((-653741147007/10000000000000 : ℚ) : ℝ) ≤ stT174 222 := by
  have hc : ((-974051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-653741147007/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-974051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c223 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-531391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1331899/2500000) (δ := 4439/500000000) (ψ := 501127/1000000) 174 150
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t223 : ((-7117589313/200000000000 : ℚ) : ℝ) ≤ stT174 223 := by
  have hc : ((-531441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7117589313/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-531441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c224 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((216557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -845319/2500000) (δ := 349/40000000) (ψ := 501127/1000000) 174 150
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t224 : ((144659801571/10000000000000 : ℚ) : ℝ) ≤ stT174 224 := by
  have hc : ((216507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144659801571/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((216507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c225 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((41893/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -360903/2500000) (δ := 349/40000000) (ψ := 501127/1000000) 174 150
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t225 : ((27926972073/500000000000 : ℚ) : ℝ) ≤ stT174 225 := by
  have hc : ((83781/100000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27926972073/500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((83781/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c226 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((981209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 485417/10000000) (δ := 701/40000000) (ψ := 501127/1000000) 174 150
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t226 : ((65265715521/1000000000000 : ℚ) : ℝ) ≤ stT174 226 := by
  have hc : ((981159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65265715521/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((981159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c227 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((142891/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 601491/2500000) (δ := 349/40000000) (ψ := 501127/1000000) 174 150
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t227 : ((189663493311/5000000000000 : ℚ) : ℝ) ≤ stT174 227 := by
  have hc : ((285757/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189663493311/5000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((285757/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c228 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-155787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 86361/200000) (δ := 349/40000000) (ψ := 501127/1000000) 174 150
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t228 : ((-103205702479/10000000000000 : ℚ) : ℝ) ≤ stT174 228 := by
  have hc : ((-155837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103205702479/10000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-155837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c229 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-397169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 777723/1250000) (δ := 349/40000000) (ψ := 501127/1000000) 174 150
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t229 : ((-131236670943/2500000000000 : ℚ) : ℝ) ≤ stT174 229 := by
  have hc : ((-198597/250000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131236670943/2500000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-198597/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c230 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-497231/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3795377/5000000) (δ := 8817/1000000000) (ψ := 501127/1000000) 174 151
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t230 : ((-40985144817/625000000000 : ℚ) : ℝ) ≤ stT174 230 := by
  have hc : ((-62157/62500 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40985144817/625000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-62157/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c231 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-652307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -114071/200000) (δ := 8817/1000000000) (ψ := 501127/1000000) 174 151
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t231 : ((-13413112277/312500000000 : ℚ) : ℝ) ≤ stT174 231 := by
  have hc : ((-652357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13413112277/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-652357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c232 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((1639/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -956131/2500000) (δ := 8817/1000000000) (ψ := 501127/1000000) 174 151
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t232 : ((268685721/100000000000 : ℚ) : ℝ) ≤ stT174 232 := by
  have hc : ((1637/40000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268685721/100000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((1637/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c233 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((177479/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -390709/2000000) (δ := 4393/500000000) (ψ := 501127/1000000) 174 151
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t233 : ((232524061893/5000000000000 : ℚ) : ℝ) ≤ stT174 233 := by
  have hc : ((354933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((232524061893/5000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((354933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c234 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((62459/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -90571/10000000) (δ := 8817/1000000000) (ψ := 501127/1000000) 174 151
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t234 : ((8165730921/125000000000 : ℚ) : ℝ) ≤ stT174 234 := by
  have hc : ((499647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8165730921/125000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((499647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c235 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((190277/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1764443/10000000) (δ := 8817/1000000000) (ψ := 501127/1000000) 174 151
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t235 : ((31028715189/625000000000 : ℚ) : ℝ) ≤ stT174 235 := by
  have hc : ((380529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31028715189/625000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((380529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c236 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((31457/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56431/156250) (δ := 4393/500000000) (ψ := 501127/1000000) 174 151
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t236 : ((639644019/78125000000 : ℚ) : ℝ) ≤ stT174 236 := by
  have hc : ((62889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((639644019/78125000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((62889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c237 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-143127/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2725447/5000000) (δ := 8817/1000000000) (ψ := 501127/1000000) 174 151
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t237 : ((-18595825003/500000000000 : ℚ) : ℝ) ≤ stT174 237 := by
  have hc : ((-286279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18595825003/500000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-286279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c238 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-973983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3641231/5000000) (δ := 4393/500000000) (ψ := 501127/1000000) 174 151
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t238 : ((-157843021683/2500000000000 : ℚ) : ℝ) ≤ stT174 238 := by
  have hc : ((-974033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157843021683/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-974033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c239 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-219281/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -660159/1000000) (δ := 871/100000000) (ψ := 501127/1000000) 174 152
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t239 : ((-283698685189/5000000000000 : ℚ) : ℝ) ≤ stT174 239 := by
  have hc : ((-438587/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-283698685189/5000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-438587/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c240 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-67323/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4785291/10000000) (δ := 871/100000000) (ψ := 501127/1000000) 174 152
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t240 : ((-21731658417/1000000000000 : ℚ) : ℝ) ≤ stT174 240 := by
  have hc : ((-67333/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21731658417/1000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-67333/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c241 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((9277/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2976561/10000000) (δ := 871/100000000) (ψ := 501127/1000000) 174 152
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t241 : ((5975030017/250000000000 : ℚ) : ℝ) ≤ stT174 241 := by
  have hc : ((37103/100000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5975030017/250000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((37103/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c242 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((111439/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1175313/10000000) (δ := 871/100000000) (ψ := 501127/1000000) 174 152
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t242 : ((35815823043/625000000000 : ℚ) : ℝ) ≤ stT174 242 := by
  have hc : ((445731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35815823043/625000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((445731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c243 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((969553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 618497/10000000) (δ := 8893/1000000000) (ψ := 501127/1000000) 174 152
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t243 : ((1243872349/20000000000 : ℚ) : ℝ) ≤ stT174 243 := by
  have hc : ((969503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1243872349/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((969503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c244 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((114379/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 480991/2000000) (δ := 8893/1000000000) (ψ := 501127/1000000) 174 152
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t244 : ((9152150487/250000000000 : ℚ) : ℝ) ≤ stT174 244 := by
  have hc : ((114369/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9152150487/250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((114369/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c245 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-1604/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4184083/10000000) (δ := 17493/1000000000) (ψ := 501127/1000000) 174 152
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t245 : ((-32808250581/5000000000000 : ℚ) : ℝ) ≤ stT174 245 := by
  have hc : ((-51353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32808250581/5000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-51353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c246 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-725389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 595599/1000000) (δ := 871/100000000) (ψ := 501127/1000000) 174 152
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t246 : ((-462523221303/10000000000000 : ℚ) : ℝ) ≤ stT174 246 := by
  have hc : ((-725439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-462523221303/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-725439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c247 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-998579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3860349/5000000) (δ := 871/100000000) (ψ := 501127/1000000) 174 152
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t247 : ((-127082530653/2000000000000 : ℚ) : ℝ) ≤ stT174 247 := by
  have hc : ((-998629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127082530653/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-998629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c248 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-159251/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6229691/10000000) (δ := 11/1250000) (ψ := 501127/1000000) 174 153
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t248 : ((-101130894261/2000000000000 : ℚ) : ℝ) ≤ stT174 248 := by
  have hc : ((-159261/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101130894261/2000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-159261/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c249 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-43819/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -559901/1250000) (δ := 8803/1000000000) (ψ := 501127/1000000) 174 153
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t249 : ((-1111021321/80000000000 : ℚ) : ℝ) ≤ stT174 249 := by
  have hc : ((-43829/200000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1111021321/80000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-43829/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_c250 :
    |Real.cos (((174 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((114673/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -683921/2500000) (δ := 11/1250000) (ψ := 501127/1000000) 174 153
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st174_t250 : ((29007042611/1000000000000 : ℚ) : ℝ) ≤ stT174 250 := by
  have hc : ((229321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((174 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st174_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29007042611/1000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((229321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st174_p1 : ((13703/15625 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT174 (i+1) := by
  rw [Finset.sum_range_one]
  exact st174_t1

theorem st174_p2 : ((2811553993721/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT174 (i+1))
      = (∑ i ∈ Finset.range 1, stT174 (i+1)) + stT174 2 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 1
    simpa using h
  have hprev := st174_p1
  have hstep := st174_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p3 : ((10840300669759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT174 (i+1))
      = (∑ i ∈ Finset.range 2, stT174 (i+1)) + stT174 3 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 2
    simpa using h
  have hprev := st174_p2
  have hstep := st174_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p4 : ((4487497648349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT174 (i+1))
      = (∑ i ∈ Finset.range 3, stT174 (i+1)) + stT174 4 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 3
    simpa using h
  have hprev := st174_p3
  have hstep := st174_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p5 : ((2255432210069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT174 (i+1))
      = (∑ i ∈ Finset.range 4, stT174 (i+1)) + stT174 5 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 4
    simpa using h
  have hprev := st174_p4
  have hstep := st174_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p6 : ((55242358361/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT174 (i+1))
      = (∑ i ∈ Finset.range 5, stT174 (i+1)) + stT174 6 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 5
    simpa using h
  have hprev := st174_p5
  have hstep := st174_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p7 : ((38100139709/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT174 (i+1))
      = (∑ i ∈ Finset.range 6, stT174 (i+1)) + stT174 7 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 6
    simpa using h
  have hprev := st174_p6
  have hstep := st174_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p8 : ((-101754805593/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT174 (i+1))
      = (∑ i ∈ Finset.range 7, stT174 (i+1)) + stT174 8 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 7
    simpa using h
  have hprev := st174_p7
  have hstep := st174_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p9 : ((-627121796769/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT174 (i+1))
      = (∑ i ∈ Finset.range 8, stT174 (i+1)) + stT174 9 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 8
    simpa using h
  have hprev := st174_p8
  have hstep := st174_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p10 : ((-1249315804659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT174 (i+1))
      = (∑ i ∈ Finset.range 9, stT174 (i+1)) + stT174 10 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 9
    simpa using h
  have hprev := st174_p9
  have hstep := st174_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p11 : ((-1934319554319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT174 (i+1))
      = (∑ i ∈ Finset.range 10, stT174 (i+1)) + stT174 11 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 10
    simpa using h
  have hprev := st174_p10
  have hstep := st174_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p12 : ((-414652074291/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT174 (i+1))
      = (∑ i ∈ Finset.range 11, stT174 (i+1)) + stT174 12 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 11
    simpa using h
  have hprev := st174_p11
  have hstep := st174_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p13 : ((-150208001841/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT174 (i+1))
      = (∑ i ∈ Finset.range 12, stT174 (i+1)) + stT174 13 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 12
    simpa using h
  have hprev := st174_p12
  have hstep := st174_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p14 : ((584866435301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT174 (i+1))
      = (∑ i ∈ Finset.range 13, stT174 (i+1)) + stT174 14 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 13
    simpa using h
  have hprev := st174_p13
  have hstep := st174_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p15 : ((1692575435133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT174 (i+1))
      = (∑ i ∈ Finset.range 14, stT174 (i+1)) + stT174 15 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 14
    simpa using h
  have hprev := st174_p14
  have hstep := st174_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p16 : ((2633918069773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT174 (i+1))
      = (∑ i ∈ Finset.range 15, stT174 (i+1)) + stT174 16 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 15
    simpa using h
  have hprev := st174_p15
  have hstep := st174_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p17 : ((862582838393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT174 (i+1))
      = (∑ i ∈ Finset.range 16, stT174 (i+1)) + stT174 17 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 16
    simpa using h
  have hprev := st174_p16
  have hstep := st174_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p18 : ((3156735990587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT174 (i+1))
      = (∑ i ∈ Finset.range 17, stT174 (i+1)) + stT174 18 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 17
    simpa using h
  have hprev := st174_p17
  have hstep := st174_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p19 : ((186570068857/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT174 (i+1))
      = (∑ i ∈ Finset.range 18, stT174 (i+1)) + stT174 19 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 18
    simpa using h
  have hprev := st174_p18
  have hstep := st174_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p20 : ((257174211093/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT174 (i+1))
      = (∑ i ∈ Finset.range 19, stT174 (i+1)) + stT174 20 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 19
    simpa using h
  have hprev := st174_p19
  have hstep := st174_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p21 : ((2200617023/7812500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT174 (i+1))
      = (∑ i ∈ Finset.range 20, stT174 (i+1)) + stT174 21 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 20
    simpa using h
  have hprev := st174_p20
  have hstep := st174_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p22 : ((438808559/6250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT174 (i+1))
      = (∑ i ∈ Finset.range 21, stT174 (i+1)) + stT174 22 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 21
    simpa using h
  have hprev := st174_p21
  have hstep := st174_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p23 : ((89976395371/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT174 (i+1))
      = (∑ i ∈ Finset.range 22, stT174 (i+1)) + stT174 23 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 22
    simpa using h
  have hprev := st174_p22
  have hstep := st174_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p24 : ((1283234411701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT174 (i+1))
      = (∑ i ∈ Finset.range 23, stT174 (i+1)) + stT174 24 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 23
    simpa using h
  have hprev := st174_p23
  have hstep := st174_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p25 : ((2211931411701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT174 (i+1))
      = (∑ i ∈ Finset.range 24, stT174 (i+1)) + stT174 25 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 24
    simpa using h
  have hprev := st174_p24
  have hstep := st174_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p26 : ((280516104143/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT174 (i+1))
      = (∑ i ∈ Finset.range 25, stT174 (i+1)) + stT174 26 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 25
    simpa using h
  have hprev := st174_p25
  have hstep := st174_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p27 : ((314964269243/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT174 (i+1))
      = (∑ i ∈ Finset.range 26, stT174 (i+1)) + stT174 27 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 26
    simpa using h
  have hprev := st174_p26
  have hstep := st174_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p28 : ((862017538479/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT174 (i+1))
      = (∑ i ∈ Finset.range 27, stT174 (i+1)) + stT174 28 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 27
    simpa using h
  have hprev := st174_p27
  have hstep := st174_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p29 : ((24325515449/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT174 (i+1))
      = (∑ i ∈ Finset.range 28, stT174 (i+1)) + stT174 29 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 28
    simpa using h
  have hprev := st174_p28
  have hstep := st174_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p30 : ((9194730614539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT174 (i+1))
      = (∑ i ∈ Finset.range 29, stT174 (i+1)) + stT174 30 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 29
    simpa using h
  have hprev := st174_p29
  have hstep := st174_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p31 : ((2744957371823/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT174 (i+1))
      = (∑ i ∈ Finset.range 30, stT174 (i+1)) + stT174 31 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 30
    simpa using h
  have hprev := st174_p30
  have hstep := st174_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p32 : ((1548530943793/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT174 (i+1))
      = (∑ i ∈ Finset.range 31, stT174 (i+1)) + stT174 32 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 31
    simpa using h
  have hprev := st174_p31
  have hstep := st174_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p33 : ((1237598899871/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT174 (i+1))
      = (∑ i ∈ Finset.range 32, stT174 (i+1)) + stT174 33 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 32
    simpa using h
  have hprev := st174_p32
  have hstep := st174_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p34 : ((5425405394623/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT174 (i+1))
      = (∑ i ∈ Finset.range 33, stT174 (i+1)) + stT174 34 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 33
    simpa using h
  have hprev := st174_p33
  have hstep := st174_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p35 : ((963056996091/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT174 (i+1))
      = (∑ i ∈ Finset.range 34, stT174 (i+1)) + stT174 35 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 34
    simpa using h
  have hprev := st174_p34
  have hstep := st174_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p36 : ((1317104741467/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT174 (i+1))
      = (∑ i ∈ Finset.range 35, stT174 (i+1)) + stT174 36 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 35
    simpa using h
  have hprev := st174_p35
  have hstep := st174_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p37 : ((5981747436957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT174 (i+1))
      = (∑ i ∈ Finset.range 36, stT174 (i+1)) + stT174 37 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 36
    simpa using h
  have hprev := st174_p36
  have hstep := st174_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p38 : ((11058105860329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT174 (i+1))
      = (∑ i ∈ Finset.range 37, stT174 (i+1)) + stT174 38 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 37
    simpa using h
  have hprev := st174_p37
  have hstep := st174_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p39 : ((9924968260721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT174 (i+1))
      = (∑ i ∈ Finset.range 38, stT174 (i+1)) + stT174 39 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 38
    simpa using h
  have hprev := st174_p38
  have hstep := st174_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p40 : ((453123310841/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT174 (i+1))
      = (∑ i ∈ Finset.range 39, stT174 (i+1)) + stT174 40 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 39
    simpa using h
  have hprev := st174_p39
  have hstep := st174_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p41 : ((11426515930661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT174 (i+1))
      = (∑ i ∈ Finset.range 40, stT174 (i+1)) + stT174 41 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 40
    simpa using h
  have hprev := st174_p40
  have hstep := st174_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p42 : ((10041264872331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT174 (i+1))
      = (∑ i ∈ Finset.range 41, stT174 (i+1)) + stT174 42 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 41
    simpa using h
  have hprev := st174_p41
  have hstep := st174_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p43 : ((11382092683731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT174 (i+1))
      = (∑ i ∈ Finset.range 42, stT174 (i+1)) + stT174 43 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 42
    simpa using h
  have hprev := st174_p42
  have hstep := st174_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p44 : ((2211844443231/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT174 (i+1))
      = (∑ i ∈ Finset.range 43, stT174 (i+1)) + stT174 44 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 43
    simpa using h
  have hprev := st174_p43
  have hstep := st174_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p45 : ((2055261545463/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT174 (i+1))
      = (∑ i ∈ Finset.range 44, stT174 (i+1)) + stT174 45 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 44
    simpa using h
  have hprev := st174_p44
  have hstep := st174_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p46 : ((729287875767/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT174 (i+1))
      = (∑ i ∈ Finset.range 45, stT174 (i+1)) + stT174 46 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 45
    simpa using h
  have hprev := st174_p45
  have hstep := st174_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p47 : ((641307942367/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT174 (i+1))
      = (∑ i ∈ Finset.range 46, stT174 (i+1)) + stT174 47 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 46
    simpa using h
  have hprev := st174_p46
  have hstep := st174_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p48 : ((11279809820497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT174 (i+1))
      = (∑ i ∈ Finset.range 47, stT174 (i+1)) + stT174 48 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 47
    simpa using h
  have hprev := st174_p47
  have hstep := st174_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p49 : ((10806533916901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT174 (i+1))
      = (∑ i ∈ Finset.range 48, stT174 (i+1)) + stT174 49 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 48
    simpa using h
  have hprev := st174_p48
  have hstep := st174_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p50 : ((10755458164077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT174 (i+1))
      = (∑ i ∈ Finset.range 49, stT174 (i+1)) + stT174 50 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 49
    simpa using h
  have hprev := st174_p49
  have hstep := st174_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p51 : ((11222539761717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT174 (i+1))
      = (∑ i ∈ Finset.range 50, stT174 (i+1)) + stT174 51 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 50
    simpa using h
  have hprev := st174_p50
  have hstep := st174_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p52 : ((10465642745411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT174 (i+1))
      = (∑ i ∈ Finset.range 51, stT174 (i+1)) + stT174 52 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 51
    simpa using h
  have hprev := st174_p51
  have hstep := st174_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p53 : ((5700980983633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT174 (i+1))
      = (∑ i ∈ Finset.range 52, stT174 (i+1)) + stT174 53 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 52
    simpa using h
  have hprev := st174_p52
  have hstep := st174_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p54 : ((5184893088359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT174 (i+1))
      = (∑ i ∈ Finset.range 53, stT174 (i+1)) + stT174 54 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 53
    simpa using h
  have hprev := st174_p53
  have hstep := st174_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p55 : ((11435993582397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT174 (i+1))
      = (∑ i ∈ Finset.range 54, stT174 (i+1)) + stT174 55 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 54
    simpa using h
  have hprev := st174_p54
  have hstep := st174_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p56 : ((10384448258869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT174 (i+1))
      = (∑ i ∈ Finset.range 55, stT174 (i+1)) + stT174 56 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 55
    simpa using h
  have hprev := st174_p55
  have hstep := st174_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p57 : ((11374067044541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT174 (i+1))
      = (∑ i ∈ Finset.range 56, stT174 (i+1)) + stT174 57 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 56
    simpa using h
  have hprev := st174_p56
  have hstep := st174_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p58 : ((10499912403701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT174 (i+1))
      = (∑ i ∈ Finset.range 57, stT174 (i+1)) + stT174 58 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 57
    simpa using h
  have hprev := st174_p57
  have hstep := st174_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p59 : ((895421281/800000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT174 (i+1))
      = (∑ i ∈ Finset.range 58, stT174 (i+1)) + stT174 59 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 58
    simpa using h
  have hprev := st174_p58
  have hstep := st174_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p60 : ((2151439700089/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT174 (i+1))
      = (∑ i ∈ Finset.range 59, stT174 (i+1)) + stT174 60 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 59
    simpa using h
  have hprev := st174_p59
  have hstep := st174_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p61 : ((10857660014829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT174 (i+1))
      = (∑ i ∈ Finset.range 60, stT174 (i+1)) + stT174 61 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 60
    simpa using h
  have hprev := st174_p60
  have hstep := st174_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p62 : ((1115166651633/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT174 (i+1))
      = (∑ i ∈ Finset.range 61, stT174 (i+1)) + stT174 62 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 61
    simpa using h
  have hprev := st174_p61
  have hstep := st174_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p63 : ((2612351127471/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT174 (i+1))
      = (∑ i ∈ Finset.range 62, stT174 (i+1)) + stT174 63 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 62
    simpa using h
  have hprev := st174_p62
  have hstep := st174_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p64 : ((2874035814971/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT174 (i+1))
      = (∑ i ∈ Finset.range 63, stT174 (i+1)) + stT174 64 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 63
    simpa using h
  have hprev := st174_p63
  have hstep := st174_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p65 : ((513345562933/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT174 (i+1))
      = (∑ i ∈ Finset.range 64, stT174 (i+1)) + stT174 65 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 64
    simpa using h
  have hprev := st174_p64
  have hstep := st174_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p66 : ((2855710725359/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT174 (i+1))
      = (∑ i ∈ Finset.range 65, stT174 (i+1)) + stT174 66 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 65
    simpa using h
  have hprev := st174_p65
  have hstep := st174_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p67 : ((5320165075103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT174 (i+1))
      = (∑ i ∈ Finset.range 66, stT174 (i+1)) + stT174 67 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 66
    simpa using h
  have hprev := st174_p66
  have hstep := st174_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p68 : ((2699770153627/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT174 (i+1))
      = (∑ i ∈ Finset.range 67, stT174 (i+1)) + stT174 68 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 67
    simpa using h
  have hprev := st174_p67
  have hstep := st174_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p69 : ((283607516989/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT174 (i+1))
      = (∑ i ∈ Finset.range 68, stT174 (i+1)) + stT174 69 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 68
    simpa using h
  have hprev := st174_p68
  have hstep := st174_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p70 : ((2568682123697/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT174 (i+1))
      = (∑ i ∈ Finset.range 69, stT174 (i+1)) + stT174 70 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 69
    simpa using h
  have hprev := st174_p69
  have hstep := st174_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p71 : ((11435204493923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT174 (i+1))
      = (∑ i ∈ Finset.range 70, stT174 (i+1)) + stT174 71 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 70
    simpa using h
  have hprev := st174_p70
  have hstep := st174_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p72 : ((10719938455347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT174 (i+1))
      = (∑ i ∈ Finset.range 71, stT174 (i+1)) + stT174 72 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 71
    simpa using h
  have hprev := st174_p71
  have hstep := st174_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p73 : ((10615339905319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT174 (i+1))
      = (∑ i ∈ Finset.range 72, stT174 (i+1)) + stT174 73 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 72
    simpa using h
  have hprev := st174_p72
  have hstep := st174_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p74 : ((11499022773667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT174 (i+1))
      = (∑ i ∈ Finset.range 73, stT174 (i+1)) + stT174 74 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 73
    simpa using h
  have hprev := st174_p73
  have hstep := st174_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p75 : ((10349898979497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT174 (i+1))
      = (∑ i ∈ Finset.range 74, stT174 (i+1)) + stT174 75 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 74
    simpa using h
  have hprev := st174_p74
  have hstep := st174_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p76 : ((2206059035533/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT174 (i+1))
      = (∑ i ∈ Finset.range 75, stT174 (i+1)) + stT174 76 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 75
    simpa using h
  have hprev := st174_p75
  have hstep := st174_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p77 : ((2258454882539/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT174 (i+1))
      = (∑ i ∈ Finset.range 76, stT174 (i+1)) + stT174 77 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 76
    simpa using h
  have hprev := st174_p76
  have hstep := st174_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p78 : ((10268939672743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT174 (i+1))
      = (∑ i ∈ Finset.range 77, stT174 (i+1)) + stT174 78 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 77
    simpa using h
  have hprev := st174_p77
  have hstep := st174_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p79 : ((563273205317/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT174 (i+1))
      = (∑ i ∈ Finset.range 78, stT174 (i+1)) + stT174 79 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 78
    simpa using h
  have hprev := st174_p78
  have hstep := st174_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p80 : ((5557304448377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT174 (i+1))
      = (∑ i ∈ Finset.range 79, stT174 (i+1)) + stT174 80 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 79
    simpa using h
  have hprev := st174_p79
  have hstep := st174_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p81 : ((5141815782653/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT174 (i+1))
      = (∑ i ∈ Finset.range 80, stT174 (i+1)) + stT174 81 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 80
    simpa using h
  have hprev := st174_p80
  have hstep := st174_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p82 : ((5672353003583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT174 (i+1))
      = (∑ i ∈ Finset.range 81, stT174 (i+1)) + stT174 82 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 81
    simpa using h
  have hprev := st174_p81
  have hstep := st174_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p83 : ((5532432059801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT174 (i+1))
      = (∑ i ∈ Finset.range 82, stT174 (i+1)) + stT174 83 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 82
    simpa using h
  have hprev := st174_p82
  have hstep := st174_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p84 : ((5141054803531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT174 (i+1))
      = (∑ i ∈ Finset.range 83, stT174 (i+1)) + stT174 84 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 83
    simpa using h
  have hprev := st174_p83
  have hstep := st174_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p85 : ((45257899491/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT174 (i+1))
      = (∑ i ∈ Finset.range 84, stT174 (i+1)) + stT174 85 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 84
    simpa using h
  have hprev := st174_p84
  have hstep := st174_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p86 : ((5575197163807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT174 (i+1))
      = (∑ i ∈ Finset.range 85, stT174 (i+1)) + stT174 86 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 85
    simpa using h
  have hprev := st174_p85
  have hstep := st174_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p87 : ((10261575126659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT174 (i+1))
      = (∑ i ∈ Finset.range 86, stT174 (i+1)) + stT174 87 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 86
    simpa using h
  have hprev := st174_p86
  have hstep := st174_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p88 : ((11164984953081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT174 (i+1))
      = (∑ i ∈ Finset.range 87, stT174 (i+1)) + stT174 88 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 87
    simpa using h
  have hprev := st174_p87
  have hstep := st174_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p89 : ((11338177862911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT174 (i+1))
      = (∑ i ∈ Finset.range 88, stT174 (i+1)) + stT174 89 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 88
    simpa using h
  have hprev := st174_p88
  have hstep := st174_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p90 : ((644188145723/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT174 (i+1))
      = (∑ i ∈ Finset.range 89, stT174 (i+1)) + stT174 90 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 89
    simpa using h
  have hprev := st174_p89
  have hstep := st174_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p91 : ((543236600647/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT174 (i+1))
      = (∑ i ∈ Finset.range 90, stT174 (i+1)) + stT174 91 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 90
    simpa using h
  have hprev := st174_p90
  have hstep := st174_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p92 : ((89994787009/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT174 (i+1))
      = (∑ i ∈ Finset.range 91, stT174 (i+1)) + stT174 92 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 91
    simpa using h
  have hprev := st174_p91
  have hstep := st174_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p93 : ((659498161617/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT174 (i+1))
      = (∑ i ∈ Finset.range 92, stT174 (i+1)) + stT174 93 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 92
    simpa using h
  have hprev := st174_p92
  have hstep := st174_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p94 : ((5235572631843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT174 (i+1))
      = (∑ i ∈ Finset.range 93, stT174 (i+1)) + stT174 94 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 93
    simpa using h
  have hprev := st174_p93
  have hstep := st174_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p95 : ((5739100062727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT174 (i+1))
      = (∑ i ∈ Finset.range 94, stT174 (i+1)) + stT174 95 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 94
    simpa using h
  have hprev := st174_p94
  have hstep := st174_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p96 : ((2760094042529/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT174 (i+1))
      = (∑ i ∈ Finset.range 95, stT174 (i+1)) + stT174 96 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 95
    simpa using h
  have hprev := st174_p95
  have hstep := st174_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p97 : ((10248041000543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT174 (i+1))
      = (∑ i ∈ Finset.range 96, stT174 (i+1)) + stT174 97 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 96
    simpa using h
  have hprev := st174_p96
  have hstep := st174_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p98 : ((11032614947271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT174 (i+1))
      = (∑ i ∈ Finset.range 97, stT174 (i+1)) + stT174 98 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 97
    simpa using h
  have hprev := st174_p97
  have hstep := st174_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p99 : ((92013261399/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT174 (i+1))
      = (∑ i ∈ Finset.range 98, stT174 (i+1)) + stT174 99 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 98
    simpa using h
  have hprev := st174_p98
  have hstep := st174_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p100 : ((84388469399/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT174 (i+1))
      = (∑ i ∈ Finset.range 99, stT174 (i+1)) + stT174 100 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 99
    simpa using h
  have hprev := st174_p99
  have hstep := st174_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p101 : ((2080538215853/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT174 (i+1))
      = (∑ i ∈ Finset.range 100, stT174 (i+1)) + stT174 101 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 100
    simpa using h
  have hprev := st174_p100
  have hstep := st174_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p102 : ((11392782631033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT174 (i+1))
      = (∑ i ∈ Finset.range 101, stT174 (i+1)) + stT174 102 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 101
    simpa using h
  have hprev := st174_p101
  have hstep := st174_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p103 : ((11271653058143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT174 (i+1))
      = (∑ i ∈ Finset.range 102, stT174 (i+1)) + stT174 103 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 102
    simpa using h
  have hprev := st174_p102
  have hstep := st174_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p104 : ((5158824372493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT174 (i+1))
      = (∑ i ∈ Finset.range 103, stT174 (i+1)) + stT174 104 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 103
    simpa using h
  have hprev := st174_p103
  have hstep := st174_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p105 : ((5315931097843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT174 (i+1))
      = (∑ i ∈ Finset.range 104, stT174 (i+1)) + stT174 105 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 104
    simpa using h
  have hprev := st174_p104
  have hstep := st174_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p106 : ((180062516659/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT174 (i+1))
      = (∑ i ∈ Finset.range 105, stT174 (i+1)) + stT174 106 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 105
    simpa using h
  have hprev := st174_p105
  have hstep := st174_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p107 : ((5543327523899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT174 (i+1))
      = (∑ i ∈ Finset.range 106, stT174 (i+1)) + stT174 107 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 106
    simpa using h
  have hprev := st174_p106
  have hstep := st174_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p108 : ((10250217403797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT174 (i+1))
      = (∑ i ∈ Finset.range 107, stT174 (i+1)) + stT174 108 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 107
    simpa using h
  have hprev := st174_p107
  have hstep := st174_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p109 : ((10750898915299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT174 (i+1))
      = (∑ i ∈ Finset.range 108, stT174 (i+1)) + stT174 109 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 108
    simpa using h
  have hprev := st174_p108
  have hstep := st174_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p110 : ((2310882561389/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT174 (i+1))
      = (∑ i ∈ Finset.range 109, stT174 (i+1)) + stT174 110 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 109
    simpa using h
  have hprev := st174_p109
  have hstep := st174_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p111 : ((2208074512619/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT174 (i+1))
      = (∑ i ∈ Finset.range 110, stT174 (i+1)) + stT174 111 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 110
    simpa using h
  have hprev := st174_p110
  have hstep := st174_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p112 : ((10240744562743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT174 (i+1))
      = (∑ i ∈ Finset.range 111, stT174 (i+1)) + stT174 112 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 111
    simpa using h
  have hprev := st174_p111
  have hstep := st174_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p113 : ((10722643434263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT174 (i+1))
      = (∑ i ∈ Finset.range 112, stT174 (i+1)) + stT174 113 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 112
    simpa using h
  have hprev := st174_p112
  have hstep := st174_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p114 : ((5772234805399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT174 (i+1))
      = (∑ i ∈ Finset.range 113, stT174 (i+1)) + stT174 114 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 113
    simpa using h
  have hprev := st174_p113
  have hstep := st174_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p115 : ((11139658932743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT174 (i+1))
      = (∑ i ∈ Finset.range 114, stT174 (i+1)) + stT174 115 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 114
    simpa using h
  have hprev := st174_p114
  have hstep := st174_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p116 : ((2055798835783/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT174 (i+1))
      = (∑ i ∈ Finset.range 115, stT174 (i+1)) + stT174 116 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 115
    simpa using h
  have hprev := st174_p115
  have hstep := st174_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p117 : ((2111750315383/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT174 (i+1))
      = (∑ i ∈ Finset.range 116, stT174 (i+1)) + stT174 117 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 116
    simpa using h
  have hprev := st174_p116
  have hstep := st174_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p118 : ((11457582539609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT174 (i+1))
      = (∑ i ∈ Finset.range 117, stT174 (i+1)) + stT174 118 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 117
    simpa using h
  have hprev := st174_p117
  have hstep := st174_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p119 : ((5676130120701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT174 (i+1))
      = (∑ i ∈ Finset.range 118, stT174 (i+1)) + stT174 119 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 118
    simpa using h
  have hprev := st174_p118
  have hstep := st174_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p120 : ((2609835899463/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT174 (i+1))
      = (∑ i ∈ Finset.range 119, stT174 (i+1)) + stT174 120 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 119
    simpa using h
  have hprev := st174_p119
  have hstep := st174_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p121 : ((5162338156829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT174 (i+1))
      = (∑ i ∈ Finset.range 120, stT174 (i+1)) + stT174 121 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 120
    simpa using h
  have hprev := st174_p120
  have hstep := st174_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p122 : ((1399794811707/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT174 (i+1))
      = (∑ i ∈ Finset.range 121, stT174 (i+1)) + stT174 122 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 121
    simpa using h
  have hprev := st174_p121
  have hstep := st174_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p123 : ((5781131542683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT174 (i+1))
      = (∑ i ∈ Finset.range 122, stT174 (i+1)) + stT174 123 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 122
    simpa using h
  have hprev := st174_p122
  have hstep := st174_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p124 : ((1080976315677/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT174 (i+1))
      = (∑ i ∈ Finset.range 123, stT174 (i+1)) + stT174 124 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 123
    simpa using h
  have hprev := st174_p123
  have hstep := st174_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p125 : ((1019966934583/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT174 (i+1))
      = (∑ i ∈ Finset.range 124, stT174 (i+1)) + stT174 125 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 124
    simpa using h
  have hprev := st174_p124
  have hstep := st174_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p126 : ((1072871249533/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT174 (i+1))
      = (∑ i ∈ Finset.range 125, stT174 (i+1)) + stT174 126 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 125
    simpa using h
  have hprev := st174_p125
  have hstep := st174_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p127 : ((5765641258443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT174 (i+1))
      = (∑ i ∈ Finset.range 126, stT174 (i+1)) + stT174 127 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 126
    simpa using h
  have hprev := st174_p126
  have hstep := st174_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p128 : ((5662927308513/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT174 (i+1))
      = (∑ i ∈ Finset.range 127, stT174 (i+1)) + stT174 128 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 127
    simpa using h
  have hprev := st174_p127
  have hstep := st174_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p129 : ((2089099917237/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT174 (i+1))
      = (∑ i ∈ Finset.range 128, stT174 (i+1)) + stT174 129 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 128
    simpa using h
  have hprev := st174_p128
  have hstep := st174_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p130 : ((5131589596221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT174 (i+1))
      = (∑ i ∈ Finset.range 129, stT174 (i+1)) + stT174 130 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 129
    simpa using h
  have hprev := st174_p129
  have hstep := st174_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p131 : ((1105106973297/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT174 (i+1))
      = (∑ i ∈ Finset.range 130, stT174 (i+1)) + stT174 131 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 130
    simpa using h
  have hprev := st174_p130
  have hstep := st174_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p132 : ((1160800925447/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT174 (i+1))
      = (∑ i ∈ Finset.range 131, stT174 (i+1)) + stT174 132 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 131
    simpa using h
  have hprev := st174_p131
  have hstep := st174_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p133 : ((1110498313549/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT174 (i+1))
      = (∑ i ∈ Finset.range 132, stT174 (i+1)) + stT174 133 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 132
    simpa using h
  have hprev := st174_p132
  have hstep := st174_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p134 : ((1286732099177/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT174 (i+1))
      = (∑ i ∈ Finset.range 133, stT174 (i+1)) + stT174 134 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 133
    simpa using h
  have hprev := st174_p133
  have hstep := st174_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p135 : ((647355002793/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT174 (i+1))
      = (∑ i ∈ Finset.range 134, stT174 (i+1)) + stT174 135 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 134
    simpa using h
  have hprev := st174_p134
  have hstep := st174_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p136 : ((559793109117/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT174 (i+1))
      = (∑ i ∈ Finset.range 135, stT174 (i+1)) + stT174 136 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 135
    simpa using h
  have hprev := st174_p135
  have hstep := st174_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p137 : ((2322346653489/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT174 (i+1))
      = (∑ i ∈ Finset.range 136, stT174 (i+1)) + stT174 137 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 136
    simpa using h
  have hprev := st174_p136
  have hstep := st174_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p138 : ((2756772277147/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT174 (i+1))
      = (∑ i ∈ Finset.range 137, stT174 (i+1)) + stT174 138 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 137
    simpa using h
  have hprev := st174_p137
  have hstep := st174_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p139 : ((5130284417321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT174 (i+1))
      = (∑ i ∈ Finset.range 138, stT174 (i+1)) + stT174 139 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 138
    simpa using h
  have hprev := st174_p138
  have hstep := st174_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p140 : ((5180460365147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT174 (i+1))
      = (∑ i ∈ Finset.range 139, stT174 (i+1)) + stT174 140 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 139
    simpa using h
  have hprev := st174_p139
  have hstep := st174_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p141 : ((5591972398391/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT174 (i+1))
      = (∑ i ∈ Finset.range 140, stT174 (i+1)) + stT174 141 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 140
    simpa using h
  have hprev := st174_p140
  have hstep := st174_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p142 : ((1453209740831/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT174 (i+1))
      = (∑ i ∈ Finset.range 141, stT174 (i+1)) + stT174 142 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 141
    simpa using h
  have hprev := st174_p141
  have hstep := st174_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p143 : ((5554266774023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT174 (i+1))
      = (∑ i ∈ Finset.range 142, stT174 (i+1)) + stT174 143 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 142
    simpa using h
  have hprev := st174_p142
  have hstep := st174_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p144 : ((2578618436533/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT174 (i+1))
      = (∑ i ∈ Finset.range 143, stT174 (i+1)) + stT174 144 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 143
    simpa using h
  have hprev := st174_p143
  have hstep := st174_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p145 : ((2566525350823/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT174 (i+1))
      = (∑ i ∈ Finset.range 144, stT174 (i+1)) + stT174 145 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 144
    simpa using h
  have hprev := st174_p144
  have hstep := st174_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p146 : ((11017236528897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT174 (i+1))
      = (∑ i ∈ Finset.range 145, stT174 (i+1)) + stT174 146 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 145
    simpa using h
  have hprev := st174_p145
  have hstep := st174_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p147 : ((11618109625617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT174 (i+1))
      = (∑ i ∈ Finset.range 146, stT174 (i+1)) + stT174 147 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 146
    simpa using h
  have hprev := st174_p146
  have hstep := st174_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p148 : ((11325859167307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT174 (i+1))
      = (∑ i ∈ Finset.range 147, stT174 (i+1)) + stT174 148 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 147
    simpa using h
  have hprev := st174_p147
  have hstep := st174_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p149 : ((10507106418027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT174 (i+1))
      = (∑ i ∈ Finset.range 148, stT174 (i+1)) + stT174 149 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 148
    simpa using h
  have hprev := st174_p148
  have hstep := st174_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p150 : ((10157400752927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT174 (i+1))
      = (∑ i ∈ Finset.range 149, stT174 (i+1)) + stT174 150 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 149
    simpa using h
  have hprev := st174_p149
  have hstep := st174_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p151 : ((10690036391959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT174 (i+1))
      = (∑ i ∈ Finset.range 150, stT174 (i+1)) + stT174 151 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 150
    simpa using h
  have hprev := st174_p150
  have hstep := st174_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p152 : ((11466924409843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT174 (i+1))
      = (∑ i ∈ Finset.range 151, stT174 (i+1)) + stT174 152 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 151
    simpa using h
  have hprev := st174_p151
  have hstep := st174_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p153 : ((11578478659063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT174 (i+1))
      = (∑ i ∈ Finset.range 152, stT174 (i+1)) + stT174 153 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 152
    simpa using h
  have hprev := st174_p152
  have hstep := st174_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p154 : ((2725627904511/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT174 (i+1))
      = (∑ i ∈ Finset.range 153, stT174 (i+1)) + stT174 154 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 153
    simpa using h
  have hprev := st174_p153
  have hstep := st174_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p155 : ((2554478991741/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT174 (i+1))
      = (∑ i ∈ Finset.range 154, stT174 (i+1)) + stT174 155 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 154
    simpa using h
  have hprev := st174_p154
  have hstep := st174_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p156 : ((2574188546781/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT174 (i+1))
      = (∑ i ∈ Finset.range 155, stT174 (i+1)) + stT174 156 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 155
    simpa using h
  have hprev := st174_p155
  have hstep := st174_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p157 : ((2760889593277/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT174 (i+1))
      = (∑ i ∈ Finset.range 156, stT174 (i+1)) + stT174 157 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 156
    simpa using h
  have hprev := st174_p156
  have hstep := st174_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p158 : ((5814304699897/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT174 (i+1))
      = (∑ i ∈ Finset.range 157, stT174 (i+1)) + stT174 158 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 157
    simpa using h
  have hprev := st174_p157
  have hstep := st174_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p159 : ((5707956030171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT174 (i+1))
      = (∑ i ∈ Finset.range 158, stT174 (i+1)) + stT174 159 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 158
    simpa using h
  have hprev := st174_p158
  have hstep := st174_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p160 : ((1330301209509/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT174 (i+1))
      = (∑ i ∈ Finset.range 159, stT174 (i+1)) + stT174 160 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 159
    simpa using h
  have hprev := st174_p159
  have hstep := st174_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p161 : ((5068806773509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT174 (i+1))
      = (∑ i ∈ Finset.range 160, stT174 (i+1)) + stT174 161 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 160
    simpa using h
  have hprev := st174_p160
  have hstep := st174_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p162 : ((1303834823929/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT174 (i+1))
      = (∑ i ∈ Finset.range 161, stT174 (i+1)) + stT174 162 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 161
    simpa using h
  have hprev := st174_p161
  have hstep := st174_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p163 : ((700529954327/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT174 (i+1))
      = (∑ i ∈ Finset.range 162, stT174 (i+1)) + stT174 163 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 162
    simpa using h
  have hprev := st174_p162
  have hstep := st174_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p164 : ((583243698503/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT174 (i+1))
      = (∑ i ∈ Finset.range 163, stT174 (i+1)) + stT174 164 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 163
    simpa using h
  have hprev := st174_p163
  have hstep := st174_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p165 : ((283446442003/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT174 (i+1))
      = (∑ i ∈ Finset.range 164, stT174 (i+1)) + stT174 165 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 164
    simpa using h
  have hprev := st174_p164
  have hstep := st174_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p166 : ((2641133743591/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT174 (i+1))
      = (∑ i ∈ Finset.range 165, stT174 (i+1)) + stT174 166 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 165
    simpa using h
  have hprev := st174_p165
  have hstep := st174_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p167 : ((2530027706759/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT174 (i+1))
      = (∑ i ∈ Finset.range 166, stT174 (i+1)) + stT174 167 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 166
    simpa using h
  have hprev := st174_p166
  have hstep := st174_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p168 : ((2609912016431/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT174 (i+1))
      = (∑ i ∈ Finset.range 167, stT174 (i+1)) + stT174 168 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 167
    simpa using h
  have hprev := st174_p167
  have hstep := st174_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p169 : ((5602050189097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT174 (i+1))
      = (∑ i ∈ Finset.range 168, stT174 (i+1)) + stT174 169 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 168
    simpa using h
  have hprev := st174_p168
  have hstep := st174_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p170 : ((5835725712761/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT174 (i+1))
      = (∑ i ∈ Finset.range 169, stT174 (i+1)) + stT174 170 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 169
    simpa using h
  have hprev := st174_p169
  have hstep := st174_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p171 : ((5699144426601/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT174 (i+1))
      = (∑ i ∈ Finset.range 170, stT174 (i+1)) + stT174 171 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 170
    simpa using h
  have hprev := st174_p170
  have hstep := st174_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p172 : ((10649623663757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT174 (i+1))
      = (∑ i ∈ Finset.range 171, stT174 (i+1)) + stT174 172 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 171
    simpa using h
  have hprev := st174_p171
  have hstep := st174_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p173 : ((10129623012913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT174 (i+1))
      = (∑ i ∈ Finset.range 172, stT174 (i+1)) + stT174 173 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 172
    simpa using h
  have hprev := st174_p172
  have hstep := st174_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p174 : ((10316983143123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT174 (i+1))
      = (∑ i ∈ Finset.range 173, stT174 (i+1)) + stT174 174 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 173
    simpa using h
  have hprev := st174_p173
  have hstep := st174_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p175 : ((11033573405931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT174 (i+1))
      = (∑ i ∈ Finset.range 174, stT174 (i+1)) + stT174 175 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 174
    simpa using h
  have hprev := st174_p174
  have hstep := st174_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p176 : ((11625493409769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT174 (i+1))
      = (∑ i ∈ Finset.range 175, stT174 (i+1)) + stT174 176 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 175
    simpa using h
  have hprev := st174_p175
  have hstep := st174_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p177 : ((11563414884039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT174 (i+1))
      = (∑ i ∈ Finset.range 176, stT174 (i+1)) + stT174 177 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 176
    simpa using h
  have hprev := st174_p176
  have hstep := st174_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p178 : ((436338143403/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT174 (i+1))
      = (∑ i ∈ Finset.range 177, stT174 (i+1)) + stT174 178 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 177
    simpa using h
  have hprev := st174_p177
  have hstep := st174_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p179 : ((10240986510151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT174 (i+1))
      = (∑ i ∈ Finset.range 178, stT174 (i+1)) + stT174 179 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 178
    simpa using h
  have hprev := st174_p178
  have hstep := st174_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p180 : ((10140983586343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT174 (i+1))
      = (∑ i ∈ Finset.range 179, stT174 (i+1)) + stT174 180 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 179
    simpa using h
  have hprev := st174_p179
  have hstep := st174_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p181 : ((10689181493693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT174 (i+1))
      = (∑ i ∈ Finset.range 180, stT174 (i+1)) + stT174 181 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 180
    simpa using h
  have hprev := st174_p180
  have hstep := st174_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p182 : ((570647703301/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT174 (i+1))
      = (∑ i ∈ Finset.range 181, stT174 (i+1)) + stT174 182 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 181
    simpa using h
  have hprev := st174_p181
  have hstep := st174_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p183 : ((2925198723971/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT174 (i+1))
      = (∑ i ∈ Finset.range 182, stT174 (i+1)) + stT174 183 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 182
    simpa using h
  have hprev := st174_p182
  have hstep := st174_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p184 : ((5658275730077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT174 (i+1))
      = (∑ i ∈ Finset.range 183, stT174 (i+1)) + stT174 184 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 183
    simpa using h
  have hprev := st174_p183
  have hstep := st174_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p185 : ((10583620773159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT174 (i+1))
      = (∑ i ∈ Finset.range 184, stT174 (i+1)) + stT174 185 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 184
    simpa using h
  have hprev := st174_p184
  have hstep := st174_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p186 : ((2020873491651/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT174 (i+1))
      = (∑ i ∈ Finset.range 185, stT174 (i+1)) + stT174 186 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 185
    simpa using h
  have hprev := st174_p185
  have hstep := st174_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p187 : ((10264418767079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT174 (i+1))
      = (∑ i ∈ Finset.range 186, stT174 (i+1)) + stT174 187 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 186
    simpa using h
  have hprev := st174_p186
  have hstep := st174_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p188 : ((10929694992047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT174 (i+1))
      = (∑ i ∈ Finset.range 187, stT174 (i+1)) + stT174 188 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 187
    simpa using h
  have hprev := st174_p187
  have hstep := st174_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p189 : ((11567659964783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT174 (i+1))
      = (∑ i ∈ Finset.range 188, stT174 (i+1)) + stT174 189 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 188
    simpa using h
  have hprev := st174_p188
  have hstep := st174_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p190 : ((11677190880311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT174 (i+1))
      = (∑ i ∈ Finset.range 189, stT174 (i+1)) + stT174 190 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 189
    simpa using h
  have hprev := st174_p189
  have hstep := st174_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p191 : ((11177731659361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT174 (i+1))
      = (∑ i ∈ Finset.range 190, stT174 (i+1)) + stT174 191 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 190
    simpa using h
  have hprev := st174_p190
  have hstep := st174_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p192 : ((10459584260689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT174 (i+1))
      = (∑ i ∈ Finset.range 191, stT174 (i+1)) + stT174 192 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 191
    simpa using h
  have hprev := st174_p191
  have hstep := st174_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p193 : ((10072750823393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT174 (i+1))
      = (∑ i ∈ Finset.range 192, stT174 (i+1)) + stT174 193 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 192
    simpa using h
  have hprev := st174_p192
  have hstep := st174_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p194 : ((10306676616911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT174 (i+1))
      = (∑ i ∈ Finset.range 193, stT174 (i+1)) + stT174 194 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 193
    simpa using h
  have hprev := st174_p193
  have hstep := st174_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p195 : ((10980736822261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT174 (i+1))
      = (∑ i ∈ Finset.range 194, stT174 (i+1)) + stT174 195 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 194
    simpa using h
  have hprev := st174_p194
  have hstep := st174_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p196 : ((90556415717/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT174 (i+1))
      = (∑ i ∈ Finset.range 195, stT174 (i+1)) + stT174 196 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 195
    simpa using h
  have hprev := st174_p195
  have hstep := st174_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p197 : ((5845135464293/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT174 (i+1))
      = (∑ i ∈ Finset.range 196, stT174 (i+1)) + stT174 197 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 196
    simpa using h
  have hprev := st174_p196
  have hstep := st174_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p198 : ((5605129413233/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT174 (i+1))
      = (∑ i ∈ Finset.range 197, stT174 (i+1)) + stT174 198 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 197
    simpa using h
  have hprev := st174_p197
  have hstep := st174_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p199 : ((262553330089/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT174 (i+1))
      = (∑ i ∈ Finset.range 198, stT174 (i+1)) + stT174 199 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 198
    simpa using h
  have hprev := st174_p198
  have hstep := st174_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p200 : ((629587859011/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT174 (i+1))
      = (∑ i ∈ Finset.range 199, stT174 (i+1)) + stT174 200 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 199
    simpa using h
  have hprev := st174_p199
  have hstep := st174_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p201 : ((10224880698961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT174 (i+1))
      = (∑ i ∈ Finset.range 200, stT174 (i+1)) + stT174 201 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 200
    simpa using h
  have hprev := st174_p200
  have hstep := st174_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p202 : ((10845388522037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT174 (i+1))
      = (∑ i ∈ Finset.range 201, stT174 (i+1)) + stT174 202 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 201
    simpa using h
  have hprev := st174_p201
  have hstep := st174_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p203 : ((11500106451497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT174 (i+1))
      = (∑ i ∈ Finset.range 202, stT174 (i+1)) + stT174 203 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 202
    simpa using h
  have hprev := st174_p202
  have hstep := st174_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p204 : ((11738366193917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT174 (i+1))
      = (∑ i ∈ Finset.range 203, stT174 (i+1)) + stT174 204 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 203
    simpa using h
  have hprev := st174_p203
  have hstep := st174_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p205 : ((1425162662253/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT174 (i+1))
      = (∑ i ∈ Finset.range 204, stT174 (i+1)) + stT174 205 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 204
    simpa using h
  have hprev := st174_p204
  have hstep := st174_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p206 : ((13401753973/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT174 (i+1))
      = (∑ i ∈ Finset.range 205, stT174 (i+1)) + stT174 206 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 205
    simpa using h
  have hprev := st174_p205
  have hstep := st174_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p207 : ((2031306676171/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT174 (i+1))
      = (∑ i ∈ Finset.range 206, stT174 (i+1)) + stT174 207 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 206
    simpa using h
  have hprev := st174_p206
  have hstep := st174_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p208 : ((10080287675767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT174 (i+1))
      = (∑ i ∈ Finset.range 207, stT174 (i+1)) + stT174 208 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 207
    simpa using h
  have hprev := st174_p207
  have hstep := st174_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p209 : ((10538644349013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT174 (i+1))
      = (∑ i ∈ Finset.range 208, stT174 (i+1)) + stT174 209 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 208
    simpa using h
  have hprev := st174_p208
  have hstep := st174_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p210 : ((5614294293819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT174 (i+1))
      = (∑ i ∈ Finset.range 209, stT174 (i+1)) + stT174 210 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 209
    simpa using h
  have hprev := st174_p209
  have hstep := st174_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p211 : ((1170284250627/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT174 (i+1))
      = (∑ i ∈ Finset.range 210, stT174 (i+1)) + stT174 211 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 210
    simpa using h
  have hprev := st174_p210
  have hstep := st174_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p212 : ((5829900967933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT174 (i+1))
      = (∑ i ∈ Finset.range 211, stT174 (i+1)) + stT174 212 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 211
    simpa using h
  have hprev := st174_p211
  have hstep := st174_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p213 : ((556550914407/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT174 (i+1))
      = (∑ i ∈ Finset.range 212, stT174 (i+1)) + stT174 213 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 212
    simpa using h
  have hprev := st174_p212
  have hstep := st174_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p214 : ((1306598779401/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT174 (i+1))
      = (∑ i ∈ Finset.range 213, stT174 (i+1)) + stT174 214 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 213
    simpa using h
  have hprev := st174_p213
  have hstep := st174_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p215 : ((5024402520499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT174 (i+1))
      = (∑ i ∈ Finset.range 214, stT174 (i+1)) + stT174 215 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 214
    simpa using h
  have hprev := st174_p214
  have hstep := st174_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p216 : ((2033247368051/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT174 (i+1))
      = (∑ i ∈ Finset.range 215, stT174 (i+1)) + stT174 216 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 215
    simpa using h
  have hprev := st174_p215
  have hstep := st174_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p217 : ((10728919091507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT174 (i+1))
      = (∑ i ∈ Finset.range 216, stT174 (i+1)) + stT174 217 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 216
    simpa using h
  have hprev := st174_p216
  have hstep := st174_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p218 : ((2847948713283/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT174 (i+1))
      = (∑ i ∈ Finset.range 217, stT174 (i+1)) + stT174 218 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 217
    simpa using h
  have hprev := st174_p217
  have hstep := st174_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p219 : ((470212005567/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT174 (i+1))
      = (∑ i ∈ Finset.range 218, stT174 (i+1)) + stT174 219 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 218
    simpa using h
  have hprev := st174_p218
  have hstep := st174_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p220 : ((464202860967/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT174 (i+1))
      = (∑ i ∈ Finset.range 219, stT174 (i+1)) + stT174 220 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 219
    simpa using h
  have hprev := st174_p219
  have hstep := st174_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p221 : ((5517023406939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT174 (i+1))
      = (∑ i ∈ Finset.range 220, stT174 (i+1)) + stT174 221 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 220
    simpa using h
  have hprev := st174_p220
  have hstep := st174_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p222 : ((10380305666871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT174 (i+1))
      = (∑ i ∈ Finset.range 221, stT174 (i+1)) + stT174 222 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 221
    simpa using h
  have hprev := st174_p221
  have hstep := st174_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p223 : ((10024426201221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT174 (i+1))
      = (∑ i ∈ Finset.range 222, stT174 (i+1)) + stT174 223 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 222
    simpa using h
  have hprev := st174_p222
  have hstep := st174_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p224 : ((1271135750349/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT174 (i+1))
      = (∑ i ∈ Finset.range 223, stT174 (i+1)) + stT174 224 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 223
    simpa using h
  have hprev := st174_p223
  have hstep := st174_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p225 : ((2681906361063/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT174 (i+1))
      = (∑ i ∈ Finset.range 224, stT174 (i+1)) + stT174 225 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 224
    simpa using h
  have hprev := st174_p224
  have hstep := st174_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p226 : ((5690141299731/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT174 (i+1))
      = (∑ i ∈ Finset.range 225, stT174 (i+1)) + stT174 226 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 225
    simpa using h
  have hprev := st174_p225
  have hstep := st174_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p227 : ((2939902396521/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT174 (i+1))
      = (∑ i ∈ Finset.range 226, stT174 (i+1)) + stT174 227 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 226
    simpa using h
  have hprev := st174_p226
  have hstep := st174_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p228 : ((2331280776721/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT174 (i+1))
      = (∑ i ∈ Finset.range 227, stT174 (i+1)) + stT174 228 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 227
    simpa using h
  have hprev := st174_p227
  have hstep := st174_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p229 : ((11131457199833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT174 (i+1))
      = (∑ i ∈ Finset.range 228, stT174 (i+1)) + stT174 229 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 228
    simpa using h
  have hprev := st174_p228
  have hstep := st174_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p230 : ((10475694882761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT174 (i+1))
      = (∑ i ∈ Finset.range 229, stT174 (i+1)) + stT174 230 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 229
    simpa using h
  have hprev := st174_p229
  have hstep := st174_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p231 : ((10046475289897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT174 (i+1))
      = (∑ i ∈ Finset.range 230, stT174 (i+1)) + stT174 231 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 230
    simpa using h
  have hprev := st174_p230
  have hstep := st174_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p232 : ((10073343861997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT174 (i+1))
      = (∑ i ∈ Finset.range 231, stT174 (i+1)) + stT174 232 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 231
    simpa using h
  have hprev := st174_p231
  have hstep := st174_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p233 : ((10538391985783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT174 (i+1))
      = (∑ i ∈ Finset.range 232, stT174 (i+1)) + stT174 233 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 232
    simpa using h
  have hprev := st174_p232
  have hstep := st174_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p234 : ((11191650459463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT174 (i+1))
      = (∑ i ∈ Finset.range 233, stT174 (i+1)) + stT174 234 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 233
    simpa using h
  have hprev := st174_p233
  have hstep := st174_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p235 : ((11688109902487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT174 (i+1))
      = (∑ i ∈ Finset.range 234, stT174 (i+1)) + stT174 235 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 234
    simpa using h
  have hprev := st174_p234
  have hstep := st174_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p236 : ((11769984336919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT174 (i+1))
      = (∑ i ∈ Finset.range 235, stT174 (i+1)) + stT174 236 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 235
    simpa using h
  have hprev := st174_p235
  have hstep := st174_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p237 : ((11398067836859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT174 (i+1))
      = (∑ i ∈ Finset.range 236, stT174 (i+1)) + stT174 237 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 236
    simpa using h
  have hprev := st174_p236
  have hstep := st174_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p238 : ((10766695750127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT174 (i+1))
      = (∑ i ∈ Finset.range 237, stT174 (i+1)) + stT174 238 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 237
    simpa using h
  have hprev := st174_p237
  have hstep := st174_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p239 : ((10199298379749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT174 (i+1))
      = (∑ i ∈ Finset.range 238, stT174 (i+1)) + stT174 239 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 238
    simpa using h
  have hprev := st174_p238
  have hstep := st174_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p240 : ((9981981795579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT174 (i+1))
      = (∑ i ∈ Finset.range 239, stT174 (i+1)) + stT174 240 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 239
    simpa using h
  have hprev := st174_p239
  have hstep := st174_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p241 : ((10220982996259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT174 (i+1))
      = (∑ i ∈ Finset.range 240, stT174 (i+1)) + stT174 241 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 240
    simpa using h
  have hprev := st174_p240
  have hstep := st174_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p242 : ((10794036164947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT174 (i+1))
      = (∑ i ∈ Finset.range 241, stT174 (i+1)) + stT174 242 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 241
    simpa using h
  have hprev := st174_p241
  have hstep := st174_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p243 : ((11415972339447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT174 (i+1))
      = (∑ i ∈ Finset.range 242, stT174 (i+1)) + stT174 243 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 242
    simpa using h
  have hprev := st174_p242
  have hstep := st174_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p244 : ((11782058358927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT174 (i+1))
      = (∑ i ∈ Finset.range 243, stT174 (i+1)) + stT174 244 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 243
    simpa using h
  have hprev := st174_p243
  have hstep := st174_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p245 : ((2343288371553/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT174 (i+1))
      = (∑ i ∈ Finset.range 244, stT174 (i+1)) + stT174 245 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 244
    simpa using h
  have hprev := st174_p244
  have hstep := st174_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p246 : ((5626959318231/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT174 (i+1))
      = (∑ i ∈ Finset.range 245, stT174 (i+1)) + stT174 246 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 245
    simpa using h
  have hprev := st174_p245
  have hstep := st174_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p247 : ((10618505983197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT174 (i+1))
      = (∑ i ∈ Finset.range 246, stT174 (i+1)) + stT174 247 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 246
    simpa using h
  have hprev := st174_p246
  have hstep := st174_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p248 : ((2528212877973/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT174 (i+1))
      = (∑ i ∈ Finset.range 247, stT174 (i+1)) + stT174 248 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 247
    simpa using h
  have hprev := st174_p247
  have hstep := st174_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p249 : ((9973973846767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT174 (i+1))
      = (∑ i ∈ Finset.range 248, stT174 (i+1)) + stT174 249 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 248
    simpa using h
  have hprev := st174_p248
  have hstep := st174_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_p250 : ((10264044272877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT174 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT174 (i+1))
      = (∑ i ∈ Finset.range 249, stT174 (i+1)) + stT174 250 := by
    have h := Finset.sum_range_succ (fun i => stT174 (i+1)) 249
    simpa using h
  have hprev := st174_p249
  have hstep := st174_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st174_s250 :
    |Real.sin (((174 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))
      - ((-177719/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -683921/2500000) (δ := 11/1250000) (ψ := 501127/1000000) 174 153
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 174`** (evaluated boundary). -/
theorem station_174_sign : 0 < hardyG ((((174:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 174 250 (by norm_num) (by norm_num)
    ((501127/1000000 : ℚ) : ℝ)
  have hchain := st174_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT174 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((174 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((501127/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st174_c250
  have hsinb := abs_le.mp st174_s250
  have hbdy_lo : ((19527359166369/242210000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((174 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((501127/1000000 : ℚ) : ℝ))) / 2
          - ((((174:ℕ)):ℝ))
            * Real.sin (((174 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((501127/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((174:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((174:ℝ) * Real.log (250:ℝ) - ((501127/1000000 : ℚ) : ℝ))) / 2
        - ((174:ℝ)) * Real.sin ((174:ℝ) * Real.log (250:ℝ) - ((501127/1000000 : ℚ) : ℝ))
        ≥ ((154377459/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((174:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((154377459/1000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((154377459/1000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((154377459/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((174:ℕ)):ℝ))+1) * (((((174:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((1605094271/2343750000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((10264044272877/10000000000000 : ℚ) : ℝ) + ((19527359166369/242210000000000 : ℚ) : ℝ)
      - ((1605094271/2343750000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((501127/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((174:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((501127/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((174:ℕ)):ℝ)))).re
      - Real.sin ((501127/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((174:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((174:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((174:ℕ)):ℝ))
      = (((((174:ℕ)):ℝ)) * (Real.log ((((174:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((174:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_174
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
  have hθwin : |(((501127/1000000 : ℚ) : ℝ) + ((32:ℤ)) * (2*Real.pi)) - theta ((((174:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((174:ℕ)):ℝ)))
    (φ := ((501127/1000000 : ℚ) : ℝ) + ((32:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((501127/1000000 : ℚ)) : ℝ) 32).1,
    (cos_sin_shift (((501127/1000000 : ℚ)) : ℝ) 32).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_174_sign
end AxiomAudit
