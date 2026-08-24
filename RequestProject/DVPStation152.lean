import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 152` (rung-154.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT152 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((152 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-373799/500000 : ℚ) : ℝ))

theorem st152_c1 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((183331/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 373799/2000000) (δ := 1/1000000000) (ψ := -373799/500000) 152 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t1 : ((366637/500000 : ℚ) : ℝ) ≤ stT152 1 := by
  have hc : ((366637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((366637/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((366637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c2 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((759543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55327/312500) (δ := 7779/1000000000) (ψ := -373799/500000) 152 17
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t2 : ((5370425889031/10000000000000 : ℚ) : ℝ) ≤ stT152 2 := by
  have hc : ((759493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5370425889031/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((759493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c3 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-332117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2386679/5000000) (δ := 1539/200000000) (ψ := -373799/500000) 152 27
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t3 : ((-1917767171001/10000000000000 : ℚ) : ℝ) ≤ stT152 3 := by
  have hc : ((-332167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1917767171001/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-332167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c4 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-139747/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5409903/10000000) (δ := 3823/500000000) (ψ := -373799/500000) 152 34
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t4 : ((-1397595279519/5000000000000 : ℚ) : ℝ) ≤ stT152 4 := by
  have hc : ((-279519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1397595279519/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-279519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c5 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((11793/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 844849/10000000) (δ := 3891/500000000) (ψ := -373799/500000) 152 39
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t5 : ((84379348753/200000000000 : ℚ) : ℝ) ≤ stT152 5 := by
  have hc : ((94339/100000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84379348753/200000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((94339/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c6 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-487561/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1459033/2000000) (δ := 7793/1000000000) (ψ := -373799/500000) 152 43
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t6 : ((-995280778019/2500000000000 : ℚ) : ℝ) ≤ stT152 6 := by
  have hc : ((-243793/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-995280778019/2500000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-243793/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c7 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((347183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1520289/5000000) (δ := 1941/250000000) (ψ := -373799/500000) 152 47
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t7 : ((328009790163/2500000000000 : ℚ) : ℝ) ≤ stT152 7 := by
  have hc : ((347133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((328009790163/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((347133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c8 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-17757/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6658621/10000000) (δ := 97/12500000) (ψ := -373799/500000) 152 50
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t8 : ((-15696003193/50000000000 : ℚ) : ℝ) ≤ stT152 8 := by
  have hc : ((-8879/10000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15696003193/50000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-8879/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c9 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-145593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4292271/10000000) (δ := 3841/500000000) (ψ := -373799/500000) 152 53
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t9 : ((-242738381881/5000000000000 : ℚ) : ℝ) ≤ stT152 9 := by
  have hc : ((-145643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242738381881/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-145643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c10 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((87523/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2794629/10000000) (δ := 1901/250000000) (ψ := -373799/500000) 152 56
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t10 : ((276740347101/2000000000000 : ℚ) : ℝ) ≤ stT152 10 := by
  have hc : ((87513/200000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((276740347101/2000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((87513/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c11 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((694603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50183/250000) (δ := 1557/200000000) (ψ := -373799/500000) 152 58
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t11 : ((2094155779489/10000000000000 : ℚ) : ℝ) ≤ stT152 11 := by
  have hc : ((694553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2094155779489/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((694553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c12 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((108293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1827863/5000000) (δ := 477/62500000) (ψ := -373799/500000) 152 60
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t12 : ((312470588493/10000000000000 : ℚ) : ℝ) ≤ stT152 12 := by
  have hc : ((108243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((312470588493/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((108243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c13 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((30423/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 106241/400000) (δ := 1939/250000000) (ψ := -373799/500000) 152 62
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t13 : ((1349912373/10000000000 : ℚ) : ℝ) ≤ stT152 13 := by
  have hc : ((243359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1349912373/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((243359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c14 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((485723/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -598861/10000000) (δ := 7661/1000000000) (ψ := -373799/500000) 152 64
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t14 : ((162260287897/625000000000 : ℚ) : ℝ) ≤ stT152 14 := by
  have hc : ((242849/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162260287897/625000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((242849/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c15 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-680319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2898743/5000000) (δ := 483/62500000) (ψ := -373799/500000) 152 66
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t15 : ((-1756705273941/10000000000000 : ℚ) : ℝ) ≤ stT152 15 := by
  have hc : ((-680369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1756705273941/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-680369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c16 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((88799/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3019181/10000000) (δ := 381/50000000) (ψ := -373799/500000) 152 67
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t16 : ((177573/2000000 : ℚ) : ℝ) ≤ stT152 16 := by
  have hc : ((177573/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177573/2000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((177573/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c17 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-135531/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5359397/10000000) (δ := 7797/1000000000) (ψ := -373799/500000) 152 69
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t17 : ((-657482753059/5000000000000 : ℚ) : ℝ) ≤ stT152 17 := by
  have hc : ((-271087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-657482753059/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-271087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c18 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((483049/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 652831/10000000) (δ := 7699/1000000000) (ψ := -373799/500000) 152 70
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t18 : ((35578068579/156250000000 : ℚ) : ℝ) ≤ stT152 18 := by
  have hc : ((30189/31250 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35578068579/156250000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((30189/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c19 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-585393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1372601/2500000) (δ := 7611/1000000000) (ψ := -373799/500000) 152 71
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t19 : ((-671549370997/5000000000000 : ℚ) : ℝ) ≤ stT152 19 := by
  have hc : ((-585443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-671549370997/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-585443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c20 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-842997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6434069/10000000) (δ := 7777/1000000000) (ψ := -373799/500000) 152 73
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t20 : ((-471277604799/2500000000000 : ℚ) : ℝ) ≤ stT152 20 := by
  have hc : ((-843047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-471277604799/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-843047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c21 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((129727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -900439/2500000) (δ := 767/100000000) (ψ := -373799/500000) 152 74
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t21 : ((141489148253/5000000000000 : ℚ) : ℝ) ≤ stT152 21 := by
  have hc : ((129677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141489148253/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((129677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c22 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((794357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1632119/10000000) (δ := 191/25000000) (ψ := -373799/500000) 152 75
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t22 : ((1693468084149/10000000000000 : ℚ) : ℝ) ≤ stT152 22 := by
  have hc : ((794307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1693468084149/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((794307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c23 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((491979/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -224199/5000000) (δ := 7747/1000000000) (ψ := -373799/500000) 152 76
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t23 : ((64112183211/312500000000 : ℚ) : ℝ) ≤ stT152 23 := by
  have hc : ((245977/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64112183211/312500000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((245977/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c24 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((999979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8143/5000000) (δ := 7749/1000000000) (ψ := -373799/500000) 152 77
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t24 : ((2041096071889/10000000000000 : ℚ) : ℝ) ≤ stT152 24 := by
  have hc : ((999929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2041096071889/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((999929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c25 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((997429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -179317/10000000) (δ := 7641/1000000000) (ψ := -373799/500000) 152 78
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t25 : ((997379/5000000 : ℚ) : ℝ) ≤ stT152 25 := by
  have hc : ((997379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((997379/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((997379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c26 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((115453/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -491707/5000000) (δ := 7669/1000000000) (ψ := -373799/500000) 152 79
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t26 : ((905638654707/5000000000000 : ℚ) : ℝ) ≤ stT152 26 := by
  have hc : ((461787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((905638654707/5000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((461787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c27 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((73721/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2350063/10000000) (δ := 243/31250000) (ψ := -373799/500000) 152 80
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t27 : ((1134912291/10000000000 : ℚ) : ℝ) ≤ stT152 27 := by
  have hc : ((294859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1134912291/10000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((294859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c28 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-124203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4238301/10000000) (δ := 193/25000000) (ψ := -373799/500000) 152 81
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t28 : ((-234816177219/10000000000000 : ℚ) : ℝ) ≤ stT152 28 := by
  have hc : ((-124253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234816177219/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-124253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c29 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-439517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -661157/1000000) (δ := 7613/1000000000) (ψ := -373799/500000) 152 82
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t29 : ((-204052318767/1250000000000 : ℚ) : ℝ) ≤ stT152 29 := by
  have hc : ((-219771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204052318767/1250000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-219771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c30 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-403071/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6271/10000) (δ := 7613/1000000000) (ψ := -373799/500000) 152 82
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t30 : ((-45996831077/312500000000 : ℚ) : ℝ) ≤ stT152 30 := by
  have hc : ((-50387/62500 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45996831077/312500000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-50387/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c31 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((353693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3023199/10000000) (δ := 7697/1000000000) (ψ := -373799/500000) 152 83
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t31 : ((635161571079/10000000000000 : ℚ) : ℝ) ≤ stT152 31 := by
  have hc : ((353643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((635161571079/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((353643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c32 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((48469/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -620259/10000000) (δ := 3899/500000000) (ψ := -373799/500000) 152 84
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t32 : ((85677430839/500000000000 : ℚ) : ℝ) ≤ stT152 32 := by
  have hc : ((96933/100000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85677430839/500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((96933/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c33 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-279439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2317507/5000000) (δ := 7691/1000000000) (ψ := -373799/500000) 152 85
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t33 : ((-486528022953/10000000000000 : ℚ) : ℝ) ≤ stT152 33 := by
  have hc : ((-279489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-486528022953/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-279489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c34 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-224241/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3354563/5000000) (δ := 7691/1000000000) (ψ := -373799/500000) 152 85
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t34 : ((-384591612951/2500000000000 : ℚ) : ℝ) ≤ stT152 34 := by
  have hc : ((-448507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-384591612951/2500000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-448507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c35 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((345991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2016413/10000000) (δ := 7619/1000000000) (ψ := -373799/500000) 152 86
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t35 : ((73098637191/625000000000 : ℚ) : ℝ) ≤ stT152 35 := by
  have hc : ((172983/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73098637191/625000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((172983/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c36 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((73469/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -186663/625000) (δ := 3863/500000000) (ψ := -373799/500000) 152 87
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t36 : ((61215808847/1000000000000 : ℚ) : ℝ) ≤ stT152 36 := by
  have hc : ((73459/200000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61215808847/1000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((73459/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c37 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-197063/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1856253/2500000) (δ := 3863/500000000) (ψ := -373799/500000) 152 87
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t37 : ((-32398604127/200000000000 : ℚ) : ℝ) ≤ stT152 37 := by
  have hc : ((-197073/200000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32398604127/200000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-197073/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c38 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((23069/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 462741/2500000) (δ := 777/100000000) (ψ := -373799/500000) 152 88
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t38 : ((299362560453/2500000000000 : ℚ) : ℝ) ≤ stT152 38 := by
  have hc : ((369079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((299362560453/2500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((369079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c39 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-949/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3986309/10000000) (δ := 7663/1000000000) (ψ := -373799/500000) 152 89
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t39 : ((-761409591/200000000000 : ℚ) : ℝ) ≤ stT152 39 := by
  have hc : ((-951/40000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-761409591/200000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-951/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c40 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-78889/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1126891/2000000) (δ := 7663/1000000000) (ψ := -373799/500000) 152 89
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t40 : ((-498977426759/5000000000000 : ℚ) : ℝ) ≤ stT152 40 := by
  have hc : ((-315581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-498977426759/5000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-315581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c41 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((481059/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8629/125000) (δ := 239/31250000) (ψ := -373799/500000) 152 90
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t41 : ((375624298029/2500000000000 : ℚ) : ℝ) ≤ stT152 41 := by
  have hc : ((240517/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((375624298029/2500000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((240517/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c42 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-97011/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1448239/2000000) (δ := 1551/200000000) (ψ := -373799/500000) 152 91
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t42 : ((-9356186659/62500000000 : ℚ) : ℝ) ≤ stT152 42 := by
  have hc : ((-12127/12500 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9356186659/62500000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-12127/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c43 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((777473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 340079/2000000) (δ := 1551/200000000) (ψ := -373799/500000) 152 91
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t43 : ((237111682731/2000000000000 : ℚ) : ℝ) ≤ stT152 43 := by
  have hc : ((777423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237111682731/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((777423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c44 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-512271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5271559/10000000) (δ := 7741/1000000000) (ψ := -373799/500000) 152 92
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t44 : ((-772353109797/10000000000000 : ℚ) : ℝ) ≤ stT152 44 := by
  have hc : ((-512321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-772353109797/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-512321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c45 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((130257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 653621/2000000) (δ := 7741/1000000000) (ψ := -373799/500000) 152 92
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t45 : ((24267284369/625000000000 : ℚ) : ℝ) ≤ stT152 45 := by
  have hc : ((16279/62500 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24267284369/625000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((16279/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c46 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-6431/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1021969/2500000) (δ := 3817/500000000) (ψ := -373799/500000) 152 93
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t46 : ((-118617089/12500000000 : ℚ) : ℝ) ≤ stT152 46 := by
  have hc : ((-1609/25000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118617089/12500000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-1609/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c47 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-62969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2042259/5000000) (δ := 3817/500000000) (ψ := -373799/500000) 152 93
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t47 : ((-1838453287/200000000000 : ℚ) : ℝ) ≤ stT152 47 := by
  have hc : ((-63019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1838453287/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-63019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c48 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((30309/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3623153/10000000) (δ := 1919/250000000) (ψ := -373799/500000) 152 94
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t48 : ((699667371/40000000000 : ℚ) : ℝ) ≤ stT152 48 := by
  have hc : ((60593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((699667371/40000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((60593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c49 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-56907/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4212143/10000000) (δ := 1919/250000000) (ψ := -373799/500000) 152 94
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t49 : ((-5083216319/312500000000 : ℚ) : ℝ) ≤ stT152 49 := by
  have hc : ((-14233/125000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5083216319/312500000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-14233/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c50 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((541/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -954689/2500000) (δ := 973/125000000) (ψ := -373799/500000) 152 95
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t50 : ((6113642799/1000000000000 : ℚ) : ℝ) ≤ stT152 50 := by
  have hc : ((4323/100000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6113642799/1000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((4323/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c51 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((88189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 463279/1250000) (δ := 973/125000000) (ψ := -373799/500000) 152 95
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t51 : ((3085481973/250000000000 : ℚ) : ℝ) ≤ stT152 51 := by
  have hc : ((88139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3085481973/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((88139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c52 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-54953/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2311427/5000000) (δ := 241/31250000) (ψ := -373799/500000) 152 96
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t52 : ((-76219995213/2000000000000 : ℚ) : ℝ) ≤ stT152 52 := by
  have hc : ((-54963/200000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76219995213/2000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-54963/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c53 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((500877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1307731/5000000) (δ := 241/31250000) (ψ := -373799/500000) 152 96
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t53 : ((137587694267/2000000000000 : ℚ) : ℝ) ≤ stT152 53 := by
  have hc : ((500827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137587694267/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((500827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c54 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-734551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5989503/10000000) (δ := 1521/200000000) (ψ := -373799/500000) 152 97
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t54 : ((-249916402407/2500000000000 : ℚ) : ℝ) ≤ stT152 54 := by
  have hc : ((-734601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-249916402407/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-734601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c55 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((57729/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 196631/2000000) (δ := 1521/200000000) (ψ := -373799/500000) 152 97
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t55 : ((622700096993/5000000000000 : ℚ) : ℝ) ≤ stT152 55 := by
  have hc : ((461807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((622700096993/5000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((461807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c56 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-199991/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1566037/2000000) (δ := 1521/200000000) (ψ := -373799/500000) 152 97
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t56 : ((-267262736307/2000000000000 : ℚ) : ℝ) ≤ stT152 56 := by
  have hc : ((-200001/200000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-267262736307/2000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-200001/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c57 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((89571/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115193/1000000) (δ := 1541/200000000) (ψ := -373799/500000) 152 98
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t57 : ((14829129139/125000000000 : ℚ) : ℝ) ≤ stT152 57 := by
  have hc : ((44783/50000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14829129139/125000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((44783/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c58 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-287247/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2728477/5000000) (δ := 1541/200000000) (ψ := -373799/500000) 152 98
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t58 : ((-9430170217/125000000000 : ℚ) : ℝ) ≤ stT152 58 := by
  have hc : ((-35909/62500 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9430170217/125000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-35909/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c59 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((68687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1877569/5000000) (δ := 7791/1000000000) (ψ := -373799/500000) 152 99
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t59 : ((89357755293/10000000000000 : ℚ) : ℝ) ≤ stT152 59 := by
  have hc : ((68637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89357755293/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((68637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c60 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((495293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 65789/250000) (δ := 7791/1000000000) (ψ := -373799/500000) 152 99
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t60 : ((319677870771/5000000000000 : ℚ) : ℝ) ≤ stT152 60 := by
  have hc : ((495243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((319677870771/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((495243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c61 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-455831/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6795269/10000000) (δ := 1921/250000000) (ψ := -373799/500000) 152 100
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t61 : ((-36478993179/312500000000 : ℚ) : ℝ) ≤ stT152 61 := by
  have hc : ((-28491/31250 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36478993179/312500000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-28491/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c62 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((96977/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -616279/10000000) (δ := 1921/250000000) (ψ := -373799/500000) 152 100
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t62 : ((30788634243/250000000000 : ℚ) : ℝ) ≤ stT152 62 := by
  have hc : ((24243/25000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30788634243/250000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((24243/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c63 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-576757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5463873/10000000) (δ := 1921/250000000) (ψ := -373799/500000) 152 100
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t63 : ((-363354378387/5000000000000 : ℚ) : ℝ) ≤ stT152 63 := by
  have hc : ((-576807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-363354378387/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-576807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c64 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-26541/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -532467/1250000) (δ := 7627/1000000000) (ψ := -373799/500000) 152 101
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t64 : ((-33188776551/2000000000000 : ℚ) : ℝ) ≤ stT152 64 := by
  have hc : ((-26551/200000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33188776551/2000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-26551/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c65 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((39721/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 81593/500000) (δ := 7627/1000000000) (ψ := -373799/500000) 152 101
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t65 : ((98529444639/1000000000000 : ℚ) : ℝ) ≤ stT152 65 := by
  have hc : ((79437/100000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98529444639/1000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((79437/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c66 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-98589/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 743351/1000000) (δ := 7627/1000000000) (ψ := -373799/500000) 152 101
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t66 : ((-12136083351/100000000000 : ℚ) : ℝ) ≤ stT152 66 := by
  have hc : ((-49297/50000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12136083351/100000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-49297/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c67 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((8124/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2560051/10000000) (δ := 3867/500000000) (ψ := -373799/500000) 152 102
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t67 : ((158785401721/2500000000000 : ℚ) : ℝ) ≤ stT152 67 := by
  have hc : ((259943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158785401721/2500000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((259943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c68 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((4203/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3069687/10000000) (δ := 3867/500000000) (ψ := -373799/500000) 152 102
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t68 : ((20384510841/500000000000 : ℚ) : ℝ) ≤ stT152 68 := by
  have hc : ((33619/100000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20384510841/500000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((33619/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c69 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-953757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7090733/10000000) (δ := 3881/500000000) (ψ := -373799/500000) 152 103
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t69 : ((-1148249141213/10000000000000 : ℚ) : ℝ) ≤ stT152 69 := by
  have hc : ((-953807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1148249141213/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-953807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c70 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((796561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1623027/10000000) (δ := 3881/500000000) (ψ := -373799/500000) 152 103
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t70 : ((238003062377/2500000000000 : ℚ) : ℝ) ≤ stT152 70 := by
  have hc : ((796511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238003062377/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((796511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c71 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((1997/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3767121/10000000) (δ := 3881/500000000) (ψ := -373799/500000) 152 103
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t71 : ((37890356987/5000000000000 : ℚ) : ℝ) ≤ stT152 71 := by
  have hc : ((31927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37890356987/5000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((31927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c72 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-44089/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51766/78125) (δ := 1531/200000000) (ψ := -373799/500000) 152 104
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t72 : ((-6495295231/62500000000 : ℚ) : ℝ) ≤ stT152 72 := by
  have hc : ((-88183/100000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6495295231/62500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-88183/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c73 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((53157/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -692297/5000000) (δ := 1531/200000000) (ψ := -373799/500000) 152 104
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t73 : ((497695039941/5000000000000 : ℚ) : ℝ) ≤ stT152 73 := by
  have hc : ((425231/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((497695039941/5000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((425231/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c74 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((56553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1892767/5000000) (δ := 1531/200000000) (ψ := -373799/500000) 152 104
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t74 : ((16420845357/2500000000000 : ℚ) : ℝ) ≤ stT152 74 := by
  have hc : ((56503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16420845357/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((56503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c75 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-228987/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6821651/10000000) (δ := 1531/200000000) (ψ := -373799/500000) 152 105
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t75 : ((-528851903299/5000000000000 : ℚ) : ℝ) ≤ stT152 75 := by
  have hc : ((-457999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-528851903299/5000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-457999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c76 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((754837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71539/400000) (δ := 1531/200000000) (ψ := -373799/500000) 152 105
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t76 : ((432899781193/5000000000000 : ℚ) : ℝ) ≤ stT152 76 := by
  have hc : ((754787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((432899781193/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((754787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c77 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((147391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3178923/10000000) (δ := 1531/200000000) (ψ := -373799/500000) 152 105
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t77 : ((16793903043/500000000000 : ℚ) : ℝ) ≤ stT152 77 := by
  have hc : ((73683/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16793903043/500000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((73683/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c78 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-248959/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1906437/2500000) (δ := 7763/1000000000) (ψ := -373799/500000) 152 106
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t78 : ((-281904952077/2500000000000 : ℚ) : ℝ) ≤ stT152 78 := by
  have hc : ((-497943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-281904952077/2500000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-497943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c79 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((441101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87029/312500) (δ := 7763/1000000000) (ψ := -373799/500000) 152 106
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t79 : ((496220746437/10000000000000 : ℚ) : ℝ) ≤ stT152 79 := by
  have hc : ((441051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((496220746437/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((441051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c80 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((139627/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 249377/1250000) (δ := 7763/1000000000) (ψ := -373799/500000) 152 106
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t80 : ((156096413361/2000000000000 : ℚ) : ℝ) ≤ stT152 80 := by
  have hc : ((139617/200000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156096413361/2000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((139617/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c81 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-8981/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3357783/5000000) (δ := 7763/1000000000) (ψ := -373799/500000) 152 106
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t81 : ((-2494863107/25000000000 : ℚ) : ℝ) ≤ stT152 81 := by
  have hc : ((-17963/20000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2494863107/25000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-17963/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c82 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-40103/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -27061/62500) (δ := 7733/1000000000) (ψ := -373799/500000) 152 107
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t82 : ((-22150094249/1250000000000 : ℚ) : ℝ) ≤ stT152 82 := by
  have hc : ((-80231/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22150094249/1250000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-80231/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c83 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((124237/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69093/2500000) (δ := 7733/1000000000) (ψ := -373799/500000) 152 107
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t83 : ((272721777783/2500000000000 : ℚ) : ℝ) ≤ stT152 83 := by
  have hc : ((496923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272721777783/2500000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((496923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c84 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-352393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4827309/10000000) (δ := 15333/1000000000) (ψ := -373799/500000) 152 107
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t84 : ((-38454703287/1000000000000 : ℚ) : ℝ) ≤ stT152 84 := by
  have hc : ((-352443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38454703287/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-352443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c85 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-831959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6383563/10000000) (δ := 3813/500000000) (ψ := -373799/500000) 152 108
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t85 : ((-902441057877/10000000000000 : ℚ) : ℝ) ≤ stT152 85 := by
  have hc : ((-832009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-902441057877/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-832009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c86 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((356989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1939083/10000000) (δ := 3813/500000000) (ψ := -373799/500000) 152 108
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t86 : ((96230979807/1250000000000 : ℚ) : ℝ) ≤ stT152 86 := by
  have hc : ((89241/125000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96230979807/1250000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((89241/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c87 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((555673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2454059/10000000) (δ := 3813/500000000) (ψ := -373799/500000) 152 108
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t87 : ((37230630361/625000000000 : ℚ) : ℝ) ≤ stT152 87 := by
  have hc : ((555623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37230630361/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((555623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c88 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-911941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1359393/2000000) (δ := 3813/500000000) (ψ := -373799/500000) 152 108
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t88 : ((-243046513491/2500000000000 : ℚ) : ℝ) ≤ stT152 88 := by
  have hc : ((-911991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243046513491/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-911991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c89 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-54517/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1154297/2500000) (δ := 1921/250000000) (ψ := -373799/500000) 152 109
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t89 : ((-28899255473/1000000000000 : ℚ) : ℝ) ≤ stT152 89 := by
  have hc : ((-54527/200000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28899255473/1000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-54527/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c90 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((988989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -185667/5000000) (δ := 1921/250000000) (ψ := -373799/500000) 152 109
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t90 : ((260608172097/2500000000000 : ℚ) : ℝ) ≤ stT152 90 := by
  have hc : ((988939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260608172097/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((988939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c91 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((19871/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3827609/10000000) (δ := 3821/250000000) (ψ := -373799/500000) 152 109
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t91 : ((2600530533/625000000000 : ℚ) : ℝ) ≤ stT152 91 := by
  have hc : ((9923/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2600530533/625000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((9923/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c92 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-998717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1545463/2000000) (δ := 7791/1000000000) (ψ := -373799/500000) 152 110
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t92 : ((-1041287507491/10000000000000 : ℚ) : ℝ) ≤ stT152 92 := by
  have hc : ((-998767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1041287507491/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-998767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c93 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((1919/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3619173/10000000) (δ := 7791/1000000000) (ψ := -373799/500000) 152 110
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t93 : ((63651163233/5000000000000 : ℚ) : ℝ) ≤ stT152 93 := by
  have hc : ((61383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63651163233/5000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((61383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c94 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((984197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 445041/10000000) (δ := 7791/1000000000) (ψ := -373799/500000) 152 110
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t94 : ((1015069882887/10000000000000 : ℚ) : ℝ) ≤ stT152 94 := by
  have hc : ((984147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1015069882887/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((984147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c95 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-214031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4466239/10000000) (δ := 7791/1000000000) (ψ := -373799/500000) 152 110
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t95 : ((-219642610299/10000000000000 : ℚ) : ℝ) ≤ stT152 95 := by
  have hc : ((-214081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219642610299/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-214081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c96 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-194431/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7262631/10000000) (δ := 1541/200000000) (ψ := -373799/500000) 152 111
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t96 : ((-198450567861/2000000000000 : ℚ) : ℝ) ≤ stT152 96 := by
  have hc : ((-194441/200000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198450567861/2000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-194441/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c97 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((238567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3324767/10000000) (δ := 1541/200000000) (ψ := -373799/500000) 152 111
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t97 : ((121088640941/5000000000000 : ℚ) : ℝ) ≤ stT152 97 := by
  have hc : ((238517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121088640941/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((238517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c98 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((7791/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 572703/10000000) (δ := 1541/200000000) (ψ := -373799/500000) 152 111
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t98 : ((4918556357/50000000000 : ℚ) : ℝ) ≤ stT152 98 := by
  have hc : ((38953/40000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4918556357/50000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((38953/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c99 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-20009/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 886123/2000000) (δ := 1541/200000000) (ψ := -373799/500000) 152 111
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t99 : ((-5028707633/250000000000 : ℚ) : ℝ) ≤ stT152 99 := by
  have hc : ((-10007/50000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5028707633/250000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-10007/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c100 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-987497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3729117/5000000) (δ := 3803/500000000) (ψ := -373799/500000) 152 112
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t100 : ((-987547/10000000 : ℚ) : ℝ) ≤ stT152 100 := by
  have hc : ((-987547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-987547/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-987547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c101 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((99797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1838541/5000000) (δ := 3803/500000000) (ψ := -373799/500000) 152 112
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t101 : ((99251955639/10000000000000 : ℚ) : ℝ) ≤ stT152 101 := by
  have hc : ((99747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99251955639/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((99747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c102 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((999643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8349/1250000) (δ := 3803/500000000) (ψ := -373799/500000) 152 112
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t102 : ((989744010171/10000000000000 : ℚ) : ℝ) ≤ stT152 102 := by
  have hc : ((999593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((989744010171/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((999593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c103 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((30557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 377411/1000000) (δ := 3803/500000000) (ψ := -373799/500000) 152 112
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t103 : ((7521016257/1250000000000 : ℚ) : ℝ) ≤ stT152 103 := by
  have hc : ((7633/125000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7521016257/1250000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((7633/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c104 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-98669/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58169/78125) (δ := 3803/500000000) (ψ := -373799/500000) 152 112
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t104 : ((-48378924797/500000000000 : ℚ) : ℝ) ≤ stT152 104 := by
  have hc : ((-49337/50000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48378924797/500000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-49337/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c105 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-34493/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4625921/10000000) (δ := 7713/1000000000) (ψ := -373799/500000) 152 113
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t105 : ((-134671410297/5000000000000 : ℚ) : ℝ) ≤ stT152 105 := by
  have hc : ((-137997/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134671410297/5000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-137997/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c106 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((458639/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -204803/2000000) (δ := 7713/1000000000) (ψ := -373799/500000) 152 113
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t106 : ((44544489899/500000000000 : ℚ) : ℝ) ≤ stT152 106 := by
  have hc : ((229307/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44544489899/500000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((229307/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c107 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((131343/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2544109/10000000) (δ := 7713/1000000000) (ψ := -373799/500000) 152 113
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t107 : ((15870240281/312500000000 : ℚ) : ℝ) ≤ stT152 107 := by
  have hc : ((262661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15870240281/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((262661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c108 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-189593/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6079021/10000000) (δ := 7713/1000000000) (ψ := -373799/500000) 152 113
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t108 : ((-364896163961/5000000000000 : ℚ) : ℝ) ≤ stT152 108 := by
  have hc : ((-379211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-364896163961/5000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-379211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c109 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-96331/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1225327/2000000) (δ := 7783/1000000000) (ψ := -373799/500000) 152 114
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t109 : ((-369097676623/5000000000000 : ℚ) : ℝ) ≤ stT152 109 := by
  have hc : ((-385349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-369097676623/5000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-385349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c110 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((486677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -531257/2000000) (δ := 7783/1000000000) (ψ := -373799/500000) 152 114
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t110 : ((231990176337/5000000000000 : ℚ) : ℝ) ≤ stT152 110 := by
  have hc : ((486627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((231990176337/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((486627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c111 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((29731/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 782677/10000000) (δ := 7783/1000000000) (ψ := -373799/500000) 152 114
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t111 : ((451486459347/5000000000000 : ℚ) : ℝ) ≤ stT152 111 := by
  have hc : ((475671/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((451486459347/5000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((475671/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c112 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-52653/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 838149/2000000) (δ := 7783/1000000000) (ψ := -373799/500000) 152 114
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t112 : ((-1555502323/156250000000 : ℚ) : ℝ) ≤ stT152 112 := by
  have hc : ((-26339/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1555502323/156250000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-26339/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c113 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-99349/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1513713/2000000) (δ := 7783/1000000000) (ψ := -373799/500000) 152 114
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t113 : ((-46732197117/500000000000 : ℚ) : ℝ) ≤ stT152 113 := by
  have hc : ((-49677/50000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46732197117/500000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-49677/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c114 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-42363/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -479137/1000000) (δ := 1919/250000000) (ψ := -373799/500000) 152 115
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t114 : ((-79364892761/2500000000000 : ℚ) : ℝ) ≤ stT152 114 := by
  have hc : ((-169477/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79364892761/2500000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-169477/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c115 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((415741/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -368141/2500000) (δ := 1919/250000000) (ψ := -373799/500000) 152 115
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t115 : ((12114276027/156250000000 : ℚ) : ℝ) ≤ stT152 115 := by
  have hc : ((103929/125000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12114276027/156250000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((103929/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c116 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((373589/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 454369/2500000) (δ := 1919/250000000) (ψ := -373799/500000) 152 115
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t116 : ((21677825529/312500000000 : ℚ) : ℝ) ≤ stT152 116 := by
  have hc : ((93391/125000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21677825529/312500000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((93391/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c117 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-444783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126983/250000) (δ := 1919/250000000) (ψ := -373799/500000) 152 115
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t117 : ((-411248553333/10000000000000 : ℚ) : ℝ) ≤ stT152 117 := by
  have hc : ((-444833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-411248553333/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-444833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c118 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-983163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7394577/10000000) (δ := 3817/500000000) (ψ := -373799/500000) 152 116
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t118 : ((-36204852299/400000000000 : ℚ) : ℝ) ≤ stT152 118 := by
  have hc : ((-983213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36204852299/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-983213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c119 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-26037/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4187833/10000000) (δ := 3817/500000000) (ψ := -373799/500000) 152 116
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t119 : ((-47759101201/5000000000000 : ℚ) : ℝ) ≤ stT152 119 := by
  have hc : ((-52099/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47759101201/5000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-52099/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c120 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((919829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1007879/10000000) (δ := 3817/500000000) (ψ := -373799/500000) 152 116
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t120 : ((83963865573/1000000000000 : ℚ) : ℝ) ≤ stT152 120 := by
  have hc : ((919779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83963865573/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((919779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c121 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((653751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 429133/2000000) (δ := 3817/500000000) (ψ := -373799/500000) 152 116
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t121 : ((59427304209/1000000000000 : ℚ) : ℝ) ≤ stT152 121 := by
  have hc : ((653701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59427304209/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((653701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c122 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-256427/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1054651/2000000) (δ := 3817/500000000) (ψ := -373799/500000) 152 116
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t122 : ((-29022608727/625000000000 : ℚ) : ℝ) ≤ stT152 122 := by
  have hc : ((-64113/125000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29022608727/625000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-64113/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c123 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-30573/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3666327/5000000) (δ := 3871/500000000) (ψ := -373799/500000) 152 117
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t123 : ((-44109065231/500000000000 : ℚ) : ℝ) ≤ stT152 123 := by
  have hc : ((-489193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44109065231/500000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-489193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c124 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-16389/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2127859/5000000) (δ := 3871/500000000) (ψ := -373799/500000) 152 117
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t124 : ((-58893508687/5000000000000 : ℚ) : ℝ) ≤ stT152 124 := by
  have hc : ((-65581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58893508687/5000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-65581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c125 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((886351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -601741/5000000) (δ := 3871/500000000) (ψ := -373799/500000) 152 117
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t125 : ((792731544527/10000000000000 : ℚ) : ℝ) ≤ stT152 125 := by
  have hc : ((886301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((792731544527/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((886301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c126 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((29813/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 912217/5000000) (δ := 3871/500000000) (ψ := -373799/500000) 152 117
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t126 : ((2655772557/40000000000 : ℚ) : ℝ) ≤ stT152 126 := by
  have hc : ((29811/40000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2655772557/40000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((29811/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c127 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-352791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1207093/2500000) (δ := 3871/500000000) (ψ := -373799/500000) 152 117
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t127 : ((-313095931237/10000000000000 : ℚ) : ℝ) ≤ stT152 127 := by
  have hc : ((-352841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-313095931237/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-352841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c128 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-999837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1952197/2500000) (δ := 3871/500000000) (ψ := -373799/500000) 152 117
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t128 : ((-220946030277/2500000000000 : ℚ) : ℝ) ≤ stT152 128 := by
  have hc : ((-999887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220946030277/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-999887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c129 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-394919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -247097/500000) (δ := 3877/500000000) (ψ := -373799/500000) 152 118
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t129 : ((-347750851019/10000000000000 : ℚ) : ℝ) ≤ stT152 129 := by
  have hc : ((-394969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-347750851019/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-394969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c130 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((10852/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -100379/500000) (δ := 3877/500000000) (ψ := -373799/500000) 152 118
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t130 : ((152274371431/2500000000000 : ℚ) : ℝ) ≤ stT152 130 := by
  have hc : ((347239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152274371431/2500000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((347239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c131 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((467643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 452161/5000000) (δ := 3877/500000000) (ψ := -373799/500000) 152 118
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t131 : ((25534982317/312500000000 : ℚ) : ℝ) ≤ stT152 131 := by
  have hc : ((233809/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25534982317/312500000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((233809/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c132 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((53143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 379407/1000000) (δ := 3877/500000000) (ψ := -373799/500000) 152 118
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t132 : ((11552877521/2500000000000 : ℚ) : ℝ) ≤ stT152 132 := by
  have hc : ((53093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11552877521/2500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((53093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c133 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-888473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3331003/5000000) (δ := 3877/500000000) (ψ := -373799/500000) 152 118
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t133 : ((-77044717853/1000000000000 : ℚ) : ℝ) ≤ stT152 133 := by
  have hc : ((-888523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77044717853/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-888523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c134 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-394447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -619951/1000000) (δ := 15247/1000000000) (ψ := -373799/500000) 152 119
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t134 : ((-42596516521/625000000000 : ℚ) : ℝ) ≤ stT152 134 := by
  have hc : ((-49309/62500 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42596516521/625000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-49309/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c135 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((54827/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3374229/10000000) (δ := 7647/1000000000) (ψ := -373799/500000) 152 119
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t135 : ((47176757199/2500000000000 : ℚ) : ℝ) ≤ stT152 135 := by
  have hc : ((109629/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47176757199/2500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((109629/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c136 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((974139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -569791/10000000) (δ := 7647/1000000000) (ψ := -373799/500000) 152 119
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t136 : ((208818381197/2500000000000 : ℚ) : ℝ) ≤ stT152 136 := by
  have hc : ((974089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208818381197/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((974089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c137 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((316393/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2214127/10000000) (δ := 7647/1000000000) (ψ := -373799/500000) 152 119
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t137 : ((16893200961/312500000000 : ℚ) : ℝ) ≤ stT152 137 := by
  have hc : ((19773/31250 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16893200961/312500000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((19773/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c138 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-408039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4977753/10000000) (δ := 7647/1000000000) (ψ := -373799/500000) 152 119
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t138 : ((-347388617873/10000000000000 : ℚ) : ℝ) ≤ stT152 138 := by
  have hc : ((-408089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-347388617873/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-408089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c139 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-249649/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7721467/10000000) (δ := 7647/1000000000) (ψ := -373799/500000) 152 119
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t139 : ((-423520276047/5000000000000 : ℚ) : ℝ) ≤ stT152 139 := by
  have hc : ((-499323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-423520276047/5000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-499323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c140 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-63643/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2631233/5000000) (δ := 7663/1000000000) (ψ := -373799/500000) 152 120
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t140 : ((-43034785507/1000000000000 : ℚ) : ℝ) ≤ stT152 140 := by
  have hc : ((-254597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43034785507/1000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-254597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c141 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((260343/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1278927/5000000) (δ := 7663/1000000000) (ψ := -373799/500000) 152 120
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t141 : ((109613532009/2500000000000 : ℚ) : ℝ) ≤ stT152 141 := by
  have hc : ((130159/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109613532009/2500000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((130159/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c142 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((124837/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 63841/5000000) (δ := 7663/1000000000) (ψ := -373799/500000) 152 120
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t142 : ((419022374463/5000000000000 : ℚ) : ℝ) ≤ stT152 142 := by
  have hc : ((499323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((419022374463/5000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((499323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c143 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((109427/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 279437/1000000) (δ := 7663/1000000000) (ψ := -373799/500000) 152 120
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t143 : ((91497000309/2500000000000 : ℚ) : ℝ) ≤ stT152 143 := by
  have hc : ((218829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91497000309/2500000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((218829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c144 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-569731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2721219/5000000) (δ := 7663/1000000000) (ψ := -373799/500000) 152 120
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t144 : ((-237408939927/5000000000000 : ℚ) : ℝ) ≤ stT152 144 := by
  have hc : ((-569781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237408939927/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-569781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c145 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-31131/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1527147/2000000) (δ := 777/100000000) (ψ := -373799/500000) 152 121
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t145 : ((-82733415011/1000000000000 : ℚ) : ℝ) ≤ stT152 145 := by
  have hc : ((-498121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82733415011/1000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-498121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c146 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-424869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5024033/10000000) (δ := 777/100000000) (ψ := -373799/500000) 152 121
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t146 : ((-175832756957/5000000000000 : ℚ) : ℝ) ≤ stT152 146 := by
  have hc : ((-424919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175832756957/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-424919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c147 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((281793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2430191/10000000) (δ := 777/100000000) (ψ := -373799/500000) 152 121
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t147 : ((14524893853/312500000000 : ℚ) : ℝ) ≤ stT152 147 := by
  have hc : ((35221/62500 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14524893853/312500000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((35221/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c148 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((998293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29219/2000000) (δ := 777/100000000) (ψ := -373799/500000) 152 121
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t148 : ((410274878271/5000000000000 : ℚ) : ℝ) ≤ stT152 148 := by
  have hc : ((998243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((410274878271/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((998243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c149 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((93909/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2705053/10000000) (δ := 777/100000000) (ψ := -373799/500000) 152 121
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t149 : ((76924971669/2000000000000 : ℚ) : ℝ) ≤ stT152 149 := by
  have hc : ((93899/200000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76924971669/2000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((93899/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c150 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-503753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1049367/2000000) (δ := 777/100000000) (ψ := -373799/500000) 152 121
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t150 : ((-411353638091/10000000000000 : ℚ) : ℝ) ≤ stT152 150 := by
  have hc : ((-503803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-411353638091/10000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-503803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c151 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-49973/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7771783/10000000) (δ := 777/100000000) (ψ := -373799/500000) 152 121
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t151 : ((-81339024339/1000000000000 : ℚ) : ℝ) ≤ stT152 151 := by
  have hc : ((-99951/100000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81339024339/1000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-99951/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c152 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-141237/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1085583/2000000) (δ := 3863/500000000) (ψ := -373799/500000) 152 122
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t152 : ((-57284299723/1250000000000 : ℚ) : ℝ) ≤ stT152 152 := by
  have hc : ((-282499/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57284299723/1250000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-282499/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c153 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((386059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2936103/10000000) (δ := 3863/500000000) (ψ := -373799/500000) 152 122
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t153 : ((78017437017/2500000000000 : ℚ) : ℝ) ≤ stT152 153 := by
  have hc : ((386009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78017437017/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((386009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c154 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((491541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -460517/10000000) (δ := 3863/500000000) (ψ := -373799/500000) 152 122
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t154 : ((49509300769/625000000000 : ℚ) : ℝ) ≤ stT152 154 := by
  have hc : ((122879/125000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49509300769/625000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((122879/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c155 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((87123/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1999033/10000000) (δ := 3863/500000000) (ψ := -373799/500000) 152 122
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t155 : ((279895315273/5000000000000 : ℚ) : ℝ) ≤ stT152 155 := by
  have hc : ((348467/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((279895315273/5000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((348467/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c156 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-204853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 177711/400000) (δ := 3863/500000000) (ψ := -373799/500000) 152 122
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t156 : ((-164053742823/10000000000000 : ℚ) : ℝ) ≤ stT152 156 := by
  have hc : ((-204903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164053742823/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-204903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c157 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-36947/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6870899/10000000) (δ := 3863/500000000) (ψ := -373799/500000) 152 122
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t157 : ((-29488516563/400000000000 : ℚ) : ℝ) ≤ stT152 157 := by
  have hc : ((-36949/40000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29488516563/400000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-36949/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c158 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-105113/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -401523/625000) (δ := 3809/500000000) (ψ := -373799/500000) 152 123
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t158 : ((-167256920583/2500000000000 : ℚ) : ℝ) ≤ stT152 158 := by
  have hc : ((-420477/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167256920583/2500000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-420477/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c159 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-19971/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -503359/1250000) (δ := 3809/500000000) (ψ := -373799/500000) 152 123
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t159 : ((-991116737/312500000000 : ℚ) : ℝ) ≤ stT152 159 := by
  have hc : ((-4999/125000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-991116737/312500000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-4999/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c160 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((395679/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -205553/1250000) (δ := 3809/500000000) (ψ := -373799/500000) 152 123
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t160 : ((156395893563/2500000000000 : ℚ) : ℝ) ≤ stT152 160 := by
  have hc : ((197827/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156395893563/2500000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((197827/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c161 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((958453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 361583/5000000) (δ := 3809/500000000) (ψ := -373799/500000) 152 123
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t161 : ((75532698833/1000000000000 : ℚ) : ℝ) ≤ stT152 161 := by
  have hc : ((958403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75532698833/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((958403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c162 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((333813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1538063/5000000) (δ := 3809/500000000) (ψ := -373799/500000) 152 123
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t162 : ((131114455631/5000000000000 : ℚ) : ℝ) ≤ stT152 162 := by
  have hc : ((333763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131114455631/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((333763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c163 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-140137/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 338413/625000) (δ := 3809/500000000) (ψ := -373799/500000) 152 123
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t163 : ((-219547275039/5000000000000 : ℚ) : ℝ) ≤ stT152 163 := by
  have hc : ((-280299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219547275039/5000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-280299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c164 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-499469/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1934691/2500000) (δ := 3809/500000000) (ψ := -373799/500000) 152 123
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t164 : ((-195019690143/2500000000000 : ℚ) : ℝ) ≤ stT152 164 := by
  have hc : ((-249747/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195019690143/2500000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-249747/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c165 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-19961/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5659179/10000000) (δ := 1923/250000000) (ψ := -373799/500000) 152 124
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t165 : ((-248653359099/5000000000000 : ℚ) : ℝ) ≤ stT152 165 := by
  have hc : ((-319401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-248653359099/5000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-319401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c166 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((223647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -672621/2000000) (δ := 1923/250000000) (ψ := -373799/500000) 152 124
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t166 : ((3470896231/200000000000 : ℚ) : ℝ) ≤ stT152 166 := by
  have hc : ((223597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3470896231/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((223597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c167 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((453999/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1080787/10000000) (δ := 1923/250000000) (ψ := -373799/500000) 152 124
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t167 : ((175647761301/2500000000000 : ℚ) : ℝ) ≤ stT152 167 := by
  have hc : ((226987/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175647761301/2500000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((226987/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c168 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((889229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1187851/10000000) (δ := 1923/250000000) (ψ := -373799/500000) 152 124
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t168 : ((171503956341/2500000000000 : ℚ) : ℝ) ≤ stT152 168 := by
  have hc : ((889179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171503956341/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((889179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c169 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((4809/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 137723/400000) (δ := 1923/250000000) (ψ := -373799/500000) 152 124
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t169 : ((1479306213/100000000000 : ℚ) : ℝ) ≤ stT152 169 := by
  have hc : ((19231/100000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1479306213/100000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((19231/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c170 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-646653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5684961/10000000) (δ := 1923/250000000) (ψ := -373799/500000) 152 124
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t170 : ((-99199713279/2000000000000 : ℚ) : ℝ) ≤ stT152 170 := by
  have hc : ((-646703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99199713279/2000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-646703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c171 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-199943/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -974283/1250000) (δ := 7799/1000000000) (ψ := -373799/500000) 152 125
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t171 : ((-1911350727/25000000000 : ℚ) : ℝ) ≤ stT152 171 := by
  have hc : ((-199953/200000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1911350727/25000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-199953/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c172 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-613601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2789261/5000000) (δ := 7799/1000000000) (ψ := -373799/500000) 152 125
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t172 : ((-467904591943/10000000000000 : ℚ) : ℝ) ≤ stT152 172 := by
  have hc : ((-613651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-467904591943/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-613651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c173 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((218763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -421953/1250000) (δ := 7799/1000000000) (ψ := -373799/500000) 152 125
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t173 : ((33256842641/2000000000000 : ℚ) : ℝ) ≤ stT152 173 := by
  have hc : ((218713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33256842641/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((218713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c174 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((889673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -592709/5000000) (δ := 7799/1000000000) (ψ := -373799/500000) 152 125
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t174 : ((337210708527/5000000000000 : ℚ) : ℝ) ≤ stT152 174 := by
  have hc : ((889623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((337210708527/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((889623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c175 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((115283/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 124031/1250000) (δ := 7799/1000000000) (ψ := -373799/500000) 152 125
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t175 : ((43570461537/625000000000 : ℚ) : ℝ) ≤ stT152 175 := by
  have hc : ((461107/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43570461537/625000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((461107/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c176 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((75741/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 197343/625000) (δ := 7799/1000000000) (ψ := -373799/500000) 152 125
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t176 : ((57082477273/2500000000000 : ℚ) : ℝ) ≤ stT152 176 := by
  have hc : ((151457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57082477273/2500000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((151457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c177 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-525583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1327623/2500000) (δ := 7799/1000000000) (ψ := -373799/500000) 152 125
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t177 : ((-395090467551/10000000000000 : ℚ) : ℝ) ≤ stT152 177 := by
  have hc : ((-525633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-395090467551/10000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-525633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c178 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-493529/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 931417/1250000) (δ := 7799/1000000000) (ψ := -373799/500000) 152 125
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t178 : ((-46241814591/625000000000 : ℚ) : ℝ) ≤ stT152 178 := by
  have hc : ((-246777/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46241814591/625000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-246777/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c179 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-770933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3063877/5000000) (δ := 7697/1000000000) (ψ := -373799/500000) 152 126
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t179 : ((-144065112397/2500000000000 : ℚ) : ℝ) ≤ stT152 179 := by
  have hc : ((-770983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144065112397/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-770983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c180 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-33507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2005387/5000000) (δ := 7697/1000000000) (ψ := -373799/500000) 152 126
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t180 : ((-6252977823/2500000000000 : ℚ) : ℝ) ≤ stT152 180 := by
  have hc : ((-33557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6252977823/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-33557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c181 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((723319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -952749/5000000) (δ := 7697/1000000000) (ψ := -373799/500000) 152 126
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t181 : ((268800754043/5000000000000 : ℚ) : ℝ) ≤ stT152 181 := by
  have hc : ((723269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268800754043/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((723269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c182 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((997169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3763/200000) (δ := 7697/1000000000) (ψ := -373799/500000) 152 126
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t182 : ((739113461631/10000000000000 : ℚ) : ℝ) ≤ stT152 182 := by
  have hc : ((997119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((739113461631/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((997119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c183 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((61521/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56759/250000) (δ := 7697/1000000000) (ψ := -373799/500000) 152 126
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t183 : ((11368479759/250000000000 : ℚ) : ℝ) ≤ stT152 183 := by
  have hc : ((15379/25000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11368479759/250000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((15379/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c184 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-16493/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 542651/1250000) (δ := 7697/1000000000) (ψ := -373799/500000) 152 126
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t184 : ((-608124529/50000000000 : ℚ) : ℝ) ≤ stT152 184 := by
  have hc : ((-8249/50000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-608124529/50000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-8249/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c185 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-33431/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3200423/5000000) (δ := 7697/1000000000) (ψ := -373799/500000) 152 126
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t185 : ((-4916088619/80000000000 : ℚ) : ℝ) ≤ stT152 185 := by
  have hc : ((-33433/40000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4916088619/80000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-33433/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c186 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-971777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7258613/10000000) (δ := 7613/1000000000) (ψ := -373799/500000) 152 127
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t186 : ((-178144635543/2500000000000 : ℚ) : ℝ) ≤ stT152 186 := by
  have hc : ((-971827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178144635543/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-971827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c187 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-247409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5221053/10000000) (δ := 7613/1000000000) (ψ := -373799/500000) 152 127
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t187 : ((-90470901741/2500000000000 : ℚ) : ℝ) ≤ stT152 187 := by
  have hc : ((-123717/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90470901741/2500000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-123717/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c188 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((288861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3194399/10000000) (δ := 7613/1000000000) (ψ := -373799/500000) 152 127
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t188 : ((52659198441/2500000000000 : ℚ) : ℝ) ≤ stT152 188 := by
  have hc : ((288811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52659198441/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((288811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c189 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((44547/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1178461/10000000) (δ := 7613/1000000000) (ψ := -373799/500000) 152 127
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t189 : ((2025082059/31250000000 : ℚ) : ℝ) ≤ stT152 189 := by
  have hc : ((89089/100000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2025082059/31250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((89089/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c190 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((945809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 826799/10000000) (δ := 7613/1000000000) (ψ := -373799/500000) 152 127
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t190 : ((171531364071/2500000000000 : ℚ) : ℝ) ≤ stT152 190 := by
  have hc : ((945759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171531364071/2500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((945759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c191 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((4279/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2821571/10000000) (δ := 7613/1000000000) (ψ := -373799/500000) 152 127
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t191 : ((3095811359/100000000000 : ℚ) : ℝ) ≤ stT152 191 := by
  have hc : ((8557/20000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3095811359/100000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((8557/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c192 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-86091/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4805893/10000000) (δ := 7613/1000000000) (ψ := -373799/500000) 152 127
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t192 : ((-15534965677/625000000000 : ℚ) : ℝ) ≤ stT152 192 := by
  have hc : ((-172207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15534965677/625000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-172207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c193 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-454561/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6779917/10000000) (δ := 7613/1000000000) (ψ := -373799/500000) 152 127
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t193 : ((-20451142261/312500000000 : ℚ) : ℝ) ≤ stT152 193 := by
  have hc : ((-227293/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20451142261/312500000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-227293/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c194 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-93733/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3482103/5000000) (δ := 193/25000000) (ψ := -373799/500000) 152 128
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t194 : ((-33650020371/500000000000 : ℚ) : ℝ) ≤ stT152 194 := by
  have hc : ((-46869/50000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33650020371/500000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-46869/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c195 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-419953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2505237/5000000) (δ := 193/25000000) (ψ := -373799/500000) 152 128
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t195 : ((-60154089669/2000000000000 : ℚ) : ℝ) ≤ stT152 195 := by
  have hc : ((-420003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60154089669/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-420003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c196 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((337351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -191671/625000) (δ := 193/25000000) (ψ := -373799/500000) 152 128
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t196 : ((48185808957/2000000000000 : ℚ) : ℝ) ≤ stT152 196 := by
  have hc : ((337301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48185808957/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((337301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c197 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((14048/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -566439/5000000) (δ := 193/25000000) (ψ := -373799/500000) 152 128
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t197 : ((32026310217/500000000000 : ℚ) : ℝ) ≤ stT152 197 := by
  have hc : ((449511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32026310217/500000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((449511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c198 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((47517/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 98897/1250000) (δ := 193/25000000) (ψ := -373799/500000) 152 128
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t198 : ((67534164401/1000000000000 : ℚ) : ℝ) ≤ stT152 198 := by
  have hc : ((95029/100000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67534164401/1000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((95029/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c199 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((469373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 135277/500000) (δ := 193/25000000) (ψ := -373799/500000) 152 128
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t199 : ((332694157563/10000000000000 : ℚ) : ℝ) ≤ stT152 199 := by
  have hc : ((469323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((332694157563/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((469323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c200 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-269929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 461029/1000000) (δ := 193/25000000) (ψ := -373799/500000) 152 128
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t200 : ((-190904040753/10000000000000 : ℚ) : ℝ) ≤ stT152 200 := by
  have hc : ((-269979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190904040753/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-269979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c201 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-858037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3252789/5000000) (δ := 193/25000000) (ψ := -373799/500000) 152 128
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t201 : ((-302624116551/5000000000000 : ℚ) : ℝ) ≤ stT152 201 := by
  have hc : ((-858087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-302624116551/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-858087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c202 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-976983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -91457/125000) (δ := 311/40000000) (ψ := -373799/500000) 152 129
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t202 : ((-343719232367/5000000000000 : ℚ) : ℝ) ≤ stT152 202 := by
  have hc : ((-977033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-343719232367/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-977033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c203 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-142233/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2720003/5000000) (δ := 311/40000000) (ψ := -373799/500000) 152 129
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t203 : ((-199673706733/5000000000000 : ℚ) : ℝ) ≤ stT152 203 := by
  have hc : ((-284491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199673706733/5000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-284491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c204 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((2207/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1786343/5000000) (δ := 311/40000000) (ψ := -373799/500000) 152 129
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t204 : ((2471459193/250000000000 : ℚ) : ℝ) ≤ stT152 204 := by
  have hc : ((70599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2471459193/250000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((70599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c205 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((193479/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -857243/5000000) (δ := 311/40000000) (ψ := -373799/500000) 152 129
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t205 : ((27024561519/500000000000 : ℚ) : ℝ) ≤ stT152 205 := by
  have hc : ((386933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27024561519/500000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((386933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c206 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((998549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13467/1000000) (δ := 311/40000000) (ψ := -373799/500000) 152 129
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t206 : ((695687203767/10000000000000 : ℚ) : ℝ) ≤ stT152 206 := by
  have hc : ((998499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((695687203767/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((998499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c207 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((351943/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 987429/5000000) (δ := 311/40000000) (ψ := -373799/500000) 152 129
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t207 : ((15287493879/312500000000 : ℚ) : ℝ) ≤ stT152 207 := by
  have hc : ((175959/250000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15287493879/312500000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((175959/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c208 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((48301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 237887/625000) (δ := 311/40000000) (ψ := -373799/500000) 152 129
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t208 : ((267648297/80000000000 : ℚ) : ℝ) ≤ stT152 208 := by
  have hc : ((48251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267648297/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((48251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c209 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-629339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1407187/2500000) (δ := 311/40000000) (ψ := -373799/500000) 152 129
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t209 : ((-87071562427/2000000000000 : ℚ) : ℝ) ≤ stT152 209 := by
  have hc : ((-629389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87071562427/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-629389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c210 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-246623/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3721301/5000000) (δ := 311/40000000) (ψ := -373799/500000) 152 129
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t210 : ((-170194772943/2500000000000 : ℚ) : ℝ) ≤ stT152 210 := by
  have hc : ((-493271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170194772943/2500000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-493271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c211 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-10607/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6460133/10000000) (δ := 1917/250000000) (ψ := -373799/500000) 152 130
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t211 : ((-58420773369/1000000000000 : ℚ) : ℝ) ≤ stT152 211 := by
  have hc : ((-84861/100000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58420773369/1000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-84861/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c212 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-290343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -932691/2000000) (δ := 1917/250000000) (ψ := -373799/500000) 152 130
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t212 : ((-199442783579/10000000000000 : ℚ) : ℝ) ≤ stT152 212 := by
  have hc : ((-290393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199442783579/10000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-290393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c213 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((40841/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2875213/10000000) (δ := 1917/250000000) (ψ := -373799/500000) 152 130
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t213 : ((1748771073/62500000000 : ℚ) : ℝ) ≤ stT152 213 := by
  have hc : ((10209/25000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1748771073/62500000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((10209/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c214 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((452773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1095331/10000000) (δ := 1917/250000000) (ψ := -373799/500000) 152 130
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t214 : ((15474587079/250000000000 : ℚ) : ℝ) ≤ stT152 214 := by
  have hc : ((113187/125000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15474587079/250000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((113187/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c215 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((24091/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 676229/10000000) (δ := 1917/250000000) (ψ := -373799/500000) 152 130
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t215 : ((32858129923/500000000000 : ℚ) : ℝ) ≤ stT152 215 := by
  have hc : ((96359/100000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32858129923/500000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((96359/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c216 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((560479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2439581/10000000) (δ := 1917/250000000) (ψ := -373799/500000) 152 130
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t216 : ((381323177177/10000000000000 : ℚ) : ℝ) ≤ stT152 216 := by
  have hc : ((560429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((381323177177/10000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((560429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c217 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-13363/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4194763/10000000) (δ := 1917/250000000) (ψ := -373799/500000) 152 130
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t217 : ((-7260518813/1000000000000 : ℚ) : ℝ) ≤ stT152 217 := by
  have hc : ((-53477/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7260518813/1000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-53477/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c218 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-144299/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5941889/10000000) (δ := 1917/250000000) (ψ := -373799/500000) 152 130
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t218 : ((-48869232687/1000000000000 : ℚ) : ℝ) ≤ stT152 218 := by
  have hc : ((-144309/200000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48869232687/1000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-144309/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c219 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-124701/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1536207/2000000) (δ := 1917/250000000) (ψ := -373799/500000) 152 130
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t219 : ((-168538855401/2500000000000 : ℚ) : ℝ) ≤ stT152 219 := by
  have hc : ((-498829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168538855401/2500000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-498829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c220 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-162391/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1573931/2500000) (δ := 3821/500000000) (ψ := -373799/500000) 152 131
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t220 : ((-547453771/10000000000 : ℚ) : ℝ) ≤ stT152 220 := by
  have hc : ((-162401/200000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-547453771/10000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-162401/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c221 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-51057/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1143087/2500000) (δ := 3821/500000000) (ψ := -373799/500000) 152 131
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t221 : ((-34351392091/2000000000000 : ℚ) : ℝ) ≤ stT152 221 := by
  have hc : ((-51067/200000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34351392091/2000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-51067/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c222 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((415121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3571/12500) (δ := 3821/500000000) (ψ := -373799/500000) 152 131
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t222 : ((69644348019/2500000000000 : ℚ) : ℝ) ≤ stT152 222 := by
  have hc : ((415071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69644348019/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((415071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c223 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((896243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8976/78125) (δ := 3821/500000000) (ψ := -373799/500000) 152 131
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t223 : ((600134746257/10000000000000 : ℚ) : ℝ) ≤ stT152 223 := by
  have hc : ((896193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((600134746257/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((896193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c224 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((975783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 275653/5000000) (δ := 3821/500000000) (ψ := -373799/500000) 152 131
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t224 : ((651938931149/10000000000000 : ℚ) : ℝ) ≤ stT152 224 := by
  have hc : ((975733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((651938931149/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((975733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c225 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((124699/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1121989/5000000) (δ := 3821/500000000) (ψ := -373799/500000) 152 131
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t225 : ((41562958437/1000000000000 : ℚ) : ℝ) ≤ stT152 225 := by
  have hc : ((124689/200000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41562958437/1000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((124689/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c226 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-423/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3929107/10000000) (δ := 7621/500000000) (ψ := -373799/500000) 152 131
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t226 : ((-4656337/78125000000 : ℚ) : ℝ) ≤ stT152 226 := by
  have hc : ((-14/15625 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4656337/78125000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-14/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c227 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-622501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2803413/5000000) (δ := 3821/500000000) (ψ := -373799/500000) 152 131
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t227 : ((-103300509981/2500000000000 : ℚ) : ℝ) ≤ stT152 227 := by
  have hc : ((-622551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103300509981/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-622551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c228 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-973499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3638577/5000000) (δ := 3821/500000000) (ψ := -373799/500000) 152 131
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t228 : ((-644749375583/10000000000000 : ℚ) : ℝ) ≤ stT152 228 := by
  have hc : ((-973549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-644749375583/10000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-973549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c229 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-56693/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6767777/10000000) (δ := 7749/1000000000) (ψ := -373799/500000) 152 132
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t229 : ((-299727013011/5000000000000 : ℚ) : ℝ) ≤ stT152 229 := by
  have hc : ((-453569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-299727013011/5000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-453569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c230 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-456453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5112003/10000000) (δ := 7749/1000000000) (ψ := -373799/500000) 152 132
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t230 : ((-301009404643/10000000000000 : ℚ) : ℝ) ≤ stT152 230 := by
  have hc : ((-456503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-301009404643/10000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-456503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c231 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((184371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3463411/10000000) (δ := 7749/1000000000) (ψ := -373799/500000) 152 132
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t231 : ((121274186271/10000000000000 : ℚ) : ℝ) ≤ stT152 231 := by
  have hc : ((184321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121274186271/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((184321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c232 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((11656/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1821963/10000000) (δ := 7749/1000000000) (ψ := -373799/500000) 152 132
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t232 : ((61216192611/1250000000000 : ℚ) : ℝ) ≤ stT152 232 := by
  have hc : ((372967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61216192611/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((372967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c233 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((997187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37509/2000000) (δ := 7749/1000000000) (ψ := -373799/500000) 152 132
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t233 : ((653245388577/10000000000000 : ℚ) : ℝ) ≤ stT152 233 := by
  have hc : ((997137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((653245388577/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((997137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c234 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((419337/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1439881/10000000) (δ := 7749/1000000000) (ψ := -373799/500000) 152 132
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t234 : ((428301001/7812500000 : ℚ) : ℝ) ≤ stT152 234 := by
  have hc : ((26207/31250 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((428301001/7812500000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((26207/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c235 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((169877/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3060353/10000000) (δ := 7749/1000000000) (ψ := -373799/500000) 152 132
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t235 : ((3462475483/156250000000 : ℚ) : ℝ) ≤ stT152 235 := by
  have hc : ((42463/125000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3462475483/156250000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((42463/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c236 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-294357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4673947/10000000) (δ := 7749/1000000000) (ψ := -373799/500000) 152 132
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t236 : ((-38328552923/2000000000000 : ℚ) : ℝ) ≤ stT152 236 := by
  have hc : ((-294407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38328552923/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-294407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c237 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-50527/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6280701/10000000) (δ := 7749/1000000000) (ψ := -373799/500000) 152 132
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t237 : ((-26258282637/500000000000 : ℚ) : ℝ) ≤ stT152 237 := by
  have hc : ((-404241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26258282637/500000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-404241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c238 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-999943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7827273/10000000) (δ := 7747/1000000000) (ψ := -373799/500000) 152 133
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t238 : ((-162049865643/2500000000000 : ℚ) : ℝ) ≤ stT152 238 := by
  have hc : ((-999993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162049865643/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-999993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c239 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-79729/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6233971/10000000) (δ := 7747/1000000000) (ψ := -373799/500000) 152 133
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t239 : ((-25787849349/500000000000 : ℚ) : ℝ) ≤ stT152 239 := by
  have hc : ((-39867/50000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25787849349/500000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-39867/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c240 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-284161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4647319/10000000) (δ := 7747/1000000000) (ψ := -373799/500000) 152 133
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t240 : ((-91728816039/5000000000000 : ℚ) : ℝ) ≤ stT152 240 := by
  have hc : ((-284211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91728816039/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-284211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c241 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((337147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3067279/10000000) (δ := 7747/1000000000) (ψ := -373799/500000) 152 133
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t241 : ((54285763783/2500000000000 : ℚ) : ℝ) ≤ stT152 241 := by
  have hc : ((337097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54285763783/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((337097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c242 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((826739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -59751/400000) (δ := 7747/1000000000) (ψ := -373799/500000) 152 133
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t242 : ((66426941217/1250000000000 : ℚ) : ℝ) ≤ stT152 242 := by
  have hc : ((826689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66426941217/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((826689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c243 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((999571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73231/10000000) (δ := 7747/1000000000) (ψ := -373799/500000) 152 133
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t243 : ((1282385443/20000000000 : ℚ) : ℝ) ≤ stT152 243 := by
  have hc : ((999521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1282385443/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((999521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c244 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((158789/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 326763/2000000) (δ := 7747/1000000000) (ψ := -373799/500000) 152 133
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t244 : ((12705971917/250000000000 : ℚ) : ℝ) ≤ stT152 244 := by
  have hc : ((158779/200000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12705971917/250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((158779/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c245 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((18207/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 796999/2500000) (δ := 15347/1000000000) (ψ := -373799/500000) 152 133
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t245 : ((23260037689/1250000000000 : ℚ) : ℝ) ≤ stT152 245 := by
  have hc : ((145631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23260037689/1250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((145631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c246 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-19871/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4735869/10000000) (δ := 7747/1000000000) (ψ := -373799/500000) 152 133
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t246 : ((-101370279961/5000000000000 : ℚ) : ℝ) ≤ stT152 246 := by
  have hc : ((-158993/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101370279961/5000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-158993/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c247 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-807667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6277453/10000000) (δ := 7747/1000000000) (ψ := -373799/500000) 152 133
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t247 : ((-102787642269/2000000000000 : ℚ) : ℝ) ≤ stT152 247 := by
  have hc : ((-807717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102787642269/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-807717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c248 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-124983/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1562561/2000000) (δ := 7747/1000000000) (ψ := -373799/500000) 152 133
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t248 : ((-317473194957/5000000000000 : ℚ) : ℝ) ≤ stT152 248 := by
  have hc : ((-499957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-317473194957/5000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-499957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c249 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-20701/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3183/5000) (δ := 7639/1000000000) (ψ := -373799/500000) 152 134
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t249 : ((-2099125341/40000000000 : ℚ) : ℝ) ≤ stT152 249 := by
  have hc : ((-82809/100000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2099125341/40000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-82809/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_c250 :
    |Real.cos (((152 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-358231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2421461/5000000) (δ := 7639/1000000000) (ψ := -373799/500000) 152 134
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st152_t250 : ((-28324621017/1250000000000 : ℚ) : ℝ) ≤ stT152 250 := by
  have hc : ((-358281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((152 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st152_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28324621017/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-358281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st152_p1 : ((366637/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT152 (i+1) := by
  rw [Finset.sum_range_one]
  exact st152_t1

theorem st152_p2 : ((12703165889031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT152 (i+1))
      = (∑ i ∈ Finset.range 1, stT152 (i+1)) + stT152 2 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 1
    simpa using h
  have hprev := st152_p1
  have hstep := st152_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p3 : ((1078539871803/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT152 (i+1))
      = (∑ i ∈ Finset.range 2, stT152 (i+1)) + stT152 3 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 2
    simpa using h
  have hprev := st152_p2
  have hstep := st152_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p4 : ((499388009937/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT152 (i+1))
      = (∑ i ∈ Finset.range 3, stT152 (i+1)) + stT152 4 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 3
    simpa using h
  have hprev := st152_p3
  have hstep := st152_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p5 : ((6104587798321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT152 (i+1))
      = (∑ i ∈ Finset.range 4, stT152 (i+1)) + stT152 5 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 4
    simpa using h
  have hprev := st152_p4
  have hstep := st152_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p6 : ((4114026242283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT152 (i+1))
      = (∑ i ∈ Finset.range 5, stT152 (i+1)) + stT152 6 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 5
    simpa using h
  have hprev := st152_p5
  have hstep := st152_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p7 : ((4770045822609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT152 (i+1))
      = (∑ i ∈ Finset.range 6, stT152 (i+1)) + stT152 7 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 6
    simpa using h
  have hprev := st152_p6
  have hstep := st152_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p8 : ((3200445503309/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT152 (i+1))
      = (∑ i ∈ Finset.range 7, stT152 (i+1)) + stT152 8 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 7
    simpa using h
  have hprev := st152_p7
  have hstep := st152_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p9 : ((739426780357/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT152 (i+1))
      = (∑ i ∈ Finset.range 8, stT152 (i+1)) + stT152 9 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 8
    simpa using h
  have hprev := st152_p8
  have hstep := st152_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p10 : ((7299115978361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT152 (i+1))
      = (∑ i ∈ Finset.range 9, stT152 (i+1)) + stT152 10 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 9
    simpa using h
  have hprev := st152_p9
  have hstep := st152_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p11 : ((187865435157/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT152 (i+1))
      = (∑ i ∈ Finset.range 10, stT152 (i+1)) + stT152 11 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 10
    simpa using h
  have hprev := st152_p10
  have hstep := st152_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p12 : ((9705742346343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT152 (i+1))
      = (∑ i ∈ Finset.range 11, stT152 (i+1)) + stT152 12 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 11
    simpa using h
  have hprev := st152_p11
  have hstep := st152_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p13 : ((11055654719343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT152 (i+1))
      = (∑ i ∈ Finset.range 12, stT152 (i+1)) + stT152 13 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 12
    simpa using h
  have hprev := st152_p12
  have hstep := st152_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p14 : ((2730363865139/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT152 (i+1))
      = (∑ i ∈ Finset.range 13, stT152 (i+1)) + stT152 14 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 13
    simpa using h
  have hprev := st152_p13
  have hstep := st152_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p15 : ((5947557025877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT152 (i+1))
      = (∑ i ∈ Finset.range 14, stT152 (i+1)) + stT152 15 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 14
    simpa using h
  have hprev := st152_p14
  have hstep := st152_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p16 : ((6391489525877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT152 (i+1))
      = (∑ i ∈ Finset.range 15, stT152 (i+1)) + stT152 16 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 15
    simpa using h
  have hprev := st152_p15
  have hstep := st152_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p17 : ((2867003386409/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT152 (i+1))
      = (∑ i ∈ Finset.range 16, stT152 (i+1)) + stT152 17 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 16
    simpa using h
  have hprev := st152_p16
  have hstep := st152_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p18 : ((3436252483673/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT152 (i+1))
      = (∑ i ∈ Finset.range 17, stT152 (i+1)) + stT152 18 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 17
    simpa using h
  have hprev := st152_p17
  have hstep := st152_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p19 : ((6200955596349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT152 (i+1))
      = (∑ i ∈ Finset.range 18, stT152 (i+1)) + stT152 19 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 18
    simpa using h
  have hprev := st152_p18
  have hstep := st152_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p20 : ((5258400386751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT152 (i+1))
      = (∑ i ∈ Finset.range 19, stT152 (i+1)) + stT152 20 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 19
    simpa using h
  have hprev := st152_p19
  have hstep := st152_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p21 : ((1349972383751/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT152 (i+1))
      = (∑ i ∈ Finset.range 20, stT152 (i+1)) + stT152 21 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 20
    simpa using h
  have hprev := st152_p20
  have hstep := st152_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p22 : ((12493247154157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT152 (i+1))
      = (∑ i ∈ Finset.range 21, stT152 (i+1)) + stT152 22 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 21
    simpa using h
  have hprev := st152_p21
  have hstep := st152_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p23 : ((14544837016909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT152 (i+1))
      = (∑ i ∈ Finset.range 22, stT152 (i+1)) + stT152 23 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 22
    simpa using h
  have hprev := st152_p22
  have hstep := st152_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p24 : ((8292966544399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT152 (i+1))
      = (∑ i ∈ Finset.range 23, stT152 (i+1)) + stT152 24 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 23
    simpa using h
  have hprev := st152_p23
  have hstep := st152_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p25 : ((9290345544399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT152 (i+1))
      = (∑ i ∈ Finset.range 24, stT152 (i+1)) + stT152 25 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 24
    simpa using h
  have hprev := st152_p24
  have hstep := st152_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p26 : ((5097992099553/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT152 (i+1))
      = (∑ i ∈ Finset.range 25, stT152 (i+1)) + stT152 26 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 25
    simpa using h
  have hprev := st152_p25
  have hstep := st152_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p27 : ((5381720172303/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT152 (i+1))
      = (∑ i ∈ Finset.range 26, stT152 (i+1)) + stT152 27 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 26
    simpa using h
  have hprev := st152_p26
  have hstep := st152_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p28 : ((21292064511993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT152 (i+1))
      = (∑ i ∈ Finset.range 27, stT152 (i+1)) + stT152 28 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 27
    simpa using h
  have hprev := st152_p27
  have hstep := st152_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p29 : ((19659645961857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT152 (i+1))
      = (∑ i ∈ Finset.range 28, stT152 (i+1)) + stT152 29 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 28
    simpa using h
  have hprev := st152_p28
  have hstep := st152_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p30 : ((18187747367393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT152 (i+1))
      = (∑ i ∈ Finset.range 29, stT152 (i+1)) + stT152 30 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 29
    simpa using h
  have hprev := st152_p29
  have hstep := st152_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p31 : ((2352863617309/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT152 (i+1))
      = (∑ i ∈ Finset.range 30, stT152 (i+1)) + stT152 31 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 30
    simpa using h
  have hprev := st152_p30
  have hstep := st152_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p32 : ((5134114388813/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT152 (i+1))
      = (∑ i ∈ Finset.range 31, stT152 (i+1)) + stT152 32 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 31
    simpa using h
  have hprev := st152_p31
  have hstep := st152_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p33 : ((20049929532299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT152 (i+1))
      = (∑ i ∈ Finset.range 32, stT152 (i+1)) + stT152 33 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 32
    simpa using h
  have hprev := st152_p32
  have hstep := st152_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p34 : ((3702312616099/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT152 (i+1))
      = (∑ i ∈ Finset.range 33, stT152 (i+1)) + stT152 34 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 33
    simpa using h
  have hprev := st152_p33
  have hstep := st152_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p35 : ((19681141275551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT152 (i+1))
      = (∑ i ∈ Finset.range 34, stT152 (i+1)) + stT152 35 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 34
    simpa using h
  have hprev := st152_p34
  have hstep := st152_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p36 : ((20293299364021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT152 (i+1))
      = (∑ i ∈ Finset.range 35, stT152 (i+1)) + stT152 36 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 35
    simpa using h
  have hprev := st152_p35
  have hstep := st152_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p37 : ((18673369157671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT152 (i+1))
      = (∑ i ∈ Finset.range 36, stT152 (i+1)) + stT152 37 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 36
    simpa using h
  have hprev := st152_p36
  have hstep := st152_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p38 : ((19870819399483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT152 (i+1))
      = (∑ i ∈ Finset.range 37, stT152 (i+1)) + stT152 38 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 37
    simpa using h
  have hprev := st152_p37
  have hstep := st152_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p39 : ((19832748919933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT152 (i+1))
      = (∑ i ∈ Finset.range 38, stT152 (i+1)) + stT152 39 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 38
    simpa using h
  have hprev := st152_p38
  have hstep := st152_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p40 : ((3766958813283/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT152 (i+1))
      = (∑ i ∈ Finset.range 39, stT152 (i+1)) + stT152 40 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 39
    simpa using h
  have hprev := st152_p39
  have hstep := st152_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p41 : ((20337291258531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT152 (i+1))
      = (∑ i ∈ Finset.range 40, stT152 (i+1)) + stT152 41 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 40
    simpa using h
  have hprev := st152_p40
  have hstep := st152_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p42 : ((18840301393091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT152 (i+1))
      = (∑ i ∈ Finset.range 41, stT152 (i+1)) + stT152 42 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 41
    simpa using h
  have hprev := st152_p41
  have hstep := st152_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p43 : ((10012929903373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT152 (i+1))
      = (∑ i ∈ Finset.range 42, stT152 (i+1)) + stT152 43 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 42
    simpa using h
  have hprev := st152_p42
  have hstep := st152_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p44 : ((19253506696949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT152 (i+1))
      = (∑ i ∈ Finset.range 43, stT152 (i+1)) + stT152 44 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 43
    simpa using h
  have hprev := st152_p43
  have hstep := st152_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p45 : ((19641783246853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT152 (i+1))
      = (∑ i ∈ Finset.range 44, stT152 (i+1)) + stT152 45 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 44
    simpa using h
  have hprev := st152_p44
  have hstep := st152_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p46 : ((19546889575653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT152 (i+1))
      = (∑ i ∈ Finset.range 45, stT152 (i+1)) + stT152 46 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 45
    simpa using h
  have hprev := st152_p45
  have hstep := st152_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p47 : ((19454966911303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT152 (i+1))
      = (∑ i ∈ Finset.range 46, stT152 (i+1)) + stT152 47 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 46
    simpa using h
  have hprev := st152_p46
  have hstep := st152_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p48 : ((19629883754053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT152 (i+1))
      = (∑ i ∈ Finset.range 47, stT152 (i+1)) + stT152 48 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 47
    simpa using h
  have hprev := st152_p47
  have hstep := st152_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p49 : ((3893444166369/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT152 (i+1))
      = (∑ i ∈ Finset.range 48, stT152 (i+1)) + stT152 49 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 48
    simpa using h
  have hprev := st152_p48
  have hstep := st152_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p50 : ((3905671451967/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT152 (i+1))
      = (∑ i ∈ Finset.range 49, stT152 (i+1)) + stT152 50 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 49
    simpa using h
  have hprev := st152_p49
  have hstep := st152_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p51 : ((3930355307751/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT152 (i+1))
      = (∑ i ∈ Finset.range 50, stT152 (i+1)) + stT152 51 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 50
    simpa using h
  have hprev := st152_p50
  have hstep := st152_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p52 : ((1927067656269/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT152 (i+1))
      = (∑ i ∈ Finset.range 51, stT152 (i+1)) + stT152 52 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 51
    simpa using h
  have hprev := st152_p51
  have hstep := st152_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p53 : ((798344601361/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT152 (i+1))
      = (∑ i ∈ Finset.range 52, stT152 (i+1)) + stT152 53 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 52
    simpa using h
  have hprev := st152_p52
  have hstep := st152_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p54 : ((18958949424397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT152 (i+1))
      = (∑ i ∈ Finset.range 53, stT152 (i+1)) + stT152 54 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 53
    simpa using h
  have hprev := st152_p53
  have hstep := st152_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p55 : ((20204349618383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT152 (i+1))
      = (∑ i ∈ Finset.range 54, stT152 (i+1)) + stT152 55 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 54
    simpa using h
  have hprev := st152_p54
  have hstep := st152_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p56 : ((1179252246053/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT152 (i+1))
      = (∑ i ∈ Finset.range 55, stT152 (i+1)) + stT152 56 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 55
    simpa using h
  have hprev := st152_p55
  have hstep := st152_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p57 : ((313349472937/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT152 (i+1))
      = (∑ i ∈ Finset.range 56, stT152 (i+1)) + stT152 57 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 56
    simpa using h
  have hprev := st152_p56
  have hstep := st152_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p58 : ((1206247040663/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT152 (i+1))
      = (∑ i ∈ Finset.range 57, stT152 (i+1)) + stT152 58 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 57
    simpa using h
  have hprev := st152_p57
  have hstep := st152_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p59 : ((19389310405901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT152 (i+1))
      = (∑ i ∈ Finset.range 58, stT152 (i+1)) + stT152 59 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 58
    simpa using h
  have hprev := st152_p58
  have hstep := st152_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p60 : ((20028666147443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT152 (i+1))
      = (∑ i ∈ Finset.range 59, stT152 (i+1)) + stT152 60 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 59
    simpa using h
  have hprev := st152_p59
  have hstep := st152_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p61 : ((3772267673143/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT152 (i+1))
      = (∑ i ∈ Finset.range 60, stT152 (i+1)) + stT152 61 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 60
    simpa using h
  have hprev := st152_p60
  have hstep := st152_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p62 : ((4018576747087/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT152 (i+1))
      = (∑ i ∈ Finset.range 61, stT152 (i+1)) + stT152 62 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 61
    simpa using h
  have hprev := st152_p61
  have hstep := st152_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p63 : ((19366174978661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT152 (i+1))
      = (∑ i ∈ Finset.range 62, stT152 (i+1)) + stT152 63 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 62
    simpa using h
  have hprev := st152_p62
  have hstep := st152_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p64 : ((9600115547953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT152 (i+1))
      = (∑ i ∈ Finset.range 63, stT152 (i+1)) + stT152 64 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 63
    simpa using h
  have hprev := st152_p63
  have hstep := st152_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p65 : ((2523190692787/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT152 (i+1))
      = (∑ i ∈ Finset.range 64, stT152 (i+1)) + stT152 65 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 64
    simpa using h
  have hprev := st152_p64
  have hstep := st152_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p66 : ((4742979301799/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT152 (i+1))
      = (∑ i ∈ Finset.range 65, stT152 (i+1)) + stT152 66 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 65
    simpa using h
  have hprev := st152_p65
  have hstep := st152_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p67 : ((30636029397/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT152 (i+1))
      = (∑ i ∈ Finset.range 66, stT152 (i+1)) + stT152 67 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 66
    simpa using h
  have hprev := st152_p66
  have hstep := st152_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p68 : ((200147490309/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT152 (i+1))
      = (∑ i ∈ Finset.range 67, stT152 (i+1)) + stT152 68 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 67
    simpa using h
  have hprev := st152_p67
  have hstep := st152_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p69 : ((18866499889687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT152 (i+1))
      = (∑ i ∈ Finset.range 68, stT152 (i+1)) + stT152 69 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 68
    simpa using h
  have hprev := st152_p68
  have hstep := st152_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p70 : ((3963702427839/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT152 (i+1))
      = (∑ i ∈ Finset.range 69, stT152 (i+1)) + stT152 70 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 69
    simpa using h
  have hprev := st152_p69
  have hstep := st152_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p71 : ((19894292853169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT152 (i+1))
      = (∑ i ∈ Finset.range 70, stT152 (i+1)) + stT152 71 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 70
    simpa using h
  have hprev := st152_p70
  have hstep := st152_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p72 : ((18855045616209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT152 (i+1))
      = (∑ i ∈ Finset.range 71, stT152 (i+1)) + stT152 72 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 71
    simpa using h
  have hprev := st152_p71
  have hstep := st152_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p73 : ((19850435696091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT152 (i+1))
      = (∑ i ∈ Finset.range 72, stT152 (i+1)) + stT152 73 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 72
    simpa using h
  have hprev := st152_p72
  have hstep := st152_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p74 : ((19916119077519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT152 (i+1))
      = (∑ i ∈ Finset.range 73, stT152 (i+1)) + stT152 74 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 73
    simpa using h
  have hprev := st152_p73
  have hstep := st152_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p75 : ((18858415270921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT152 (i+1))
      = (∑ i ∈ Finset.range 74, stT152 (i+1)) + stT152 75 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 74
    simpa using h
  have hprev := st152_p74
  have hstep := st152_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p76 : ((19724214833307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT152 (i+1))
      = (∑ i ∈ Finset.range 75, stT152 (i+1)) + stT152 76 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 75
    simpa using h
  have hprev := st152_p75
  have hstep := st152_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p77 : ((20060092894167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT152 (i+1))
      = (∑ i ∈ Finset.range 76, stT152 (i+1)) + stT152 77 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 76
    simpa using h
  have hprev := st152_p76
  have hstep := st152_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p78 : ((18932473085859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT152 (i+1))
      = (∑ i ∈ Finset.range 77, stT152 (i+1)) + stT152 78 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 77
    simpa using h
  have hprev := st152_p77
  have hstep := st152_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p79 : ((2428586729037/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT152 (i+1))
      = (∑ i ∈ Finset.range 78, stT152 (i+1)) + stT152 79 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 78
    simpa using h
  have hprev := st152_p78
  have hstep := st152_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p80 : ((20209175899101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT152 (i+1))
      = (∑ i ∈ Finset.range 79, stT152 (i+1)) + stT152 80 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 79
    simpa using h
  have hprev := st152_p79
  have hstep := st152_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p81 : ((19211230656301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT152 (i+1))
      = (∑ i ∈ Finset.range 80, stT152 (i+1)) + stT152 81 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 80
    simpa using h
  have hprev := st152_p80
  have hstep := st152_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p82 : ((19034029902309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT152 (i+1))
      = (∑ i ∈ Finset.range 81, stT152 (i+1)) + stT152 82 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 81
    simpa using h
  have hprev := st152_p81
  have hstep := st152_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p83 : ((20124917013441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT152 (i+1))
      = (∑ i ∈ Finset.range 82, stT152 (i+1)) + stT152 83 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 82
    simpa using h
  have hprev := st152_p82
  have hstep := st152_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p84 : ((19740369980571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT152 (i+1))
      = (∑ i ∈ Finset.range 83, stT152 (i+1)) + stT152 84 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 83
    simpa using h
  have hprev := st152_p83
  have hstep := st152_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p85 : ((9418964461347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT152 (i+1))
      = (∑ i ∈ Finset.range 84, stT152 (i+1)) + stT152 85 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 84
    simpa using h
  have hprev := st152_p84
  have hstep := st152_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p86 : ((392155535223/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT152 (i+1))
      = (∑ i ∈ Finset.range 85, stT152 (i+1)) + stT152 86 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 85
    simpa using h
  have hprev := st152_p85
  have hstep := st152_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p87 : ((10101733423463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT152 (i+1))
      = (∑ i ∈ Finset.range 86, stT152 (i+1)) + stT152 87 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 86
    simpa using h
  have hprev := st152_p86
  have hstep := st152_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p88 : ((9615640396481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT152 (i+1))
      = (∑ i ∈ Finset.range 87, stT152 (i+1)) + stT152 88 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 87
    simpa using h
  have hprev := st152_p87
  have hstep := st152_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p89 : ((2367786029779/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT152 (i+1))
      = (∑ i ∈ Finset.range 88, stT152 (i+1)) + stT152 89 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 88
    simpa using h
  have hprev := st152_p88
  have hstep := st152_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p90 : ((999236046331/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT152 (i+1))
      = (∑ i ∈ Finset.range 89, stT152 (i+1)) + stT152 90 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 89
    simpa using h
  have hprev := st152_p89
  have hstep := st152_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p91 : ((5006582353787/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT152 (i+1))
      = (∑ i ∈ Finset.range 90, stT152 (i+1)) + stT152 91 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 90
    simpa using h
  have hprev := st152_p90
  have hstep := st152_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p92 : ((18985041907657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT152 (i+1))
      = (∑ i ∈ Finset.range 91, stT152 (i+1)) + stT152 92 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 91
    simpa using h
  have hprev := st152_p91
  have hstep := st152_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p93 : ((19112344234123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT152 (i+1))
      = (∑ i ∈ Finset.range 92, stT152 (i+1)) + stT152 93 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 92
    simpa using h
  have hprev := st152_p92
  have hstep := st152_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p94 : ((2012741411701/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT152 (i+1))
      = (∑ i ∈ Finset.range 93, stT152 (i+1)) + stT152 94 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 93
    simpa using h
  have hprev := st152_p93
  have hstep := st152_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p95 : ((19907771506711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT152 (i+1))
      = (∑ i ∈ Finset.range 94, stT152 (i+1)) + stT152 95 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 94
    simpa using h
  have hprev := st152_p94
  have hstep := st152_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p96 : ((9457759333703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT152 (i+1))
      = (∑ i ∈ Finset.range 95, stT152 (i+1)) + stT152 96 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 95
    simpa using h
  have hprev := st152_p95
  have hstep := st152_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p97 : ((2394711993661/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT152 (i+1))
      = (∑ i ∈ Finset.range 96, stT152 (i+1)) + stT152 97 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 96
    simpa using h
  have hprev := st152_p96
  have hstep := st152_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p98 : ((1258837951293/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT152 (i+1))
      = (∑ i ∈ Finset.range 97, stT152 (i+1)) + stT152 98 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 97
    simpa using h
  have hprev := st152_p97
  have hstep := st152_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p99 : ((2492532364421/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT152 (i+1))
      = (∑ i ∈ Finset.range 98, stT152 (i+1)) + stT152 99 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 98
    simpa using h
  have hprev := st152_p98
  have hstep := st152_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p100 : ((2369088989421/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT152 (i+1))
      = (∑ i ∈ Finset.range 99, stT152 (i+1)) + stT152 100 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 99
    simpa using h
  have hprev := st152_p99
  have hstep := st152_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p101 : ((19051963871007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT152 (i+1))
      = (∑ i ∈ Finset.range 100, stT152 (i+1)) + stT152 101 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 100
    simpa using h
  have hprev := st152_p100
  have hstep := st152_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p102 : ((10020853940589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT152 (i+1))
      = (∑ i ∈ Finset.range 101, stT152 (i+1)) + stT152 102 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 101
    simpa using h
  have hprev := st152_p101
  have hstep := st152_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p103 : ((10050938005617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT152 (i+1))
      = (∑ i ∈ Finset.range 102, stT152 (i+1)) + stT152 103 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 102
    simpa using h
  have hprev := st152_p102
  have hstep := st152_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p104 : ((9567148757647/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT152 (i+1))
      = (∑ i ∈ Finset.range 103, stT152 (i+1)) + stT152 104 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 103
    simpa using h
  have hprev := st152_p103
  have hstep := st152_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p105 : ((188649546947/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT152 (i+1))
      = (∑ i ∈ Finset.range 104, stT152 (i+1)) + stT152 105 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 104
    simpa using h
  have hprev := st152_p104
  have hstep := st152_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p106 : ((493896112317/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT152 (i+1))
      = (∑ i ∈ Finset.range 105, stT152 (i+1)) + stT152 106 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 105
    simpa using h
  have hprev := st152_p105
  have hstep := st152_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p107 : ((2532961522709/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT152 (i+1))
      = (∑ i ∈ Finset.range 106, stT152 (i+1)) + stT152 107 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 106
    simpa using h
  have hprev := st152_p106
  have hstep := st152_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p108 : ((15627119883/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT152 (i+1))
      = (∑ i ∈ Finset.range 107, stT152 (i+1)) + stT152 108 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 107
    simpa using h
  have hprev := st152_p107
  have hstep := st152_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p109 : ((2349463062563/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT152 (i+1))
      = (∑ i ∈ Finset.range 108, stT152 (i+1)) + stT152 109 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 108
    simpa using h
  have hprev := st152_p108
  have hstep := st152_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p110 : ((9629842426589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT152 (i+1))
      = (∑ i ∈ Finset.range 109, stT152 (i+1)) + stT152 110 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 109
    simpa using h
  have hprev := st152_p109
  have hstep := st152_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p111 : ((630083055371/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT152 (i+1))
      = (∑ i ∈ Finset.range 110, stT152 (i+1)) + stT152 111 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 110
    simpa using h
  have hprev := st152_p110
  have hstep := st152_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p112 : ((25078882029/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT152 (i+1))
      = (∑ i ∈ Finset.range 111, stT152 (i+1)) + stT152 112 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 111
    simpa using h
  have hprev := st152_p111
  have hstep := st152_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p113 : ((956423084043/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT152 (i+1))
      = (∑ i ∈ Finset.range 112, stT152 (i+1)) + stT152 113 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 112
    simpa using h
  have hprev := st152_p112
  have hstep := st152_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p114 : ((2351375263727/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT152 (i+1))
      = (∑ i ∈ Finset.range 113, stT152 (i+1)) + stT152 114 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 113
    simpa using h
  have hprev := st152_p113
  have hstep := st152_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p115 : ((2448289471943/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT152 (i+1))
      = (∑ i ∈ Finset.range 114, stT152 (i+1)) + stT152 115 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 114
    simpa using h
  have hprev := st152_p114
  have hstep := st152_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p116 : ((2535000774059/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT152 (i+1))
      = (∑ i ∈ Finset.range 115, stT152 (i+1)) + stT152 116 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 115
    simpa using h
  have hprev := st152_p115
  have hstep := st152_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p117 : ((19868757639139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT152 (i+1))
      = (∑ i ∈ Finset.range 116, stT152 (i+1)) + stT152 117 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 116
    simpa using h
  have hprev := st152_p116
  have hstep := st152_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p118 : ((1185227270729/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT152 (i+1))
      = (∑ i ∈ Finset.range 117, stT152 (i+1)) + stT152 118 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 117
    simpa using h
  have hprev := st152_p117
  have hstep := st152_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p119 : ((9434059064631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT152 (i+1))
      = (∑ i ∈ Finset.range 118, stT152 (i+1)) + stT152 119 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 118
    simpa using h
  have hprev := st152_p118
  have hstep := st152_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p120 : ((615867399531/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT152 (i+1))
      = (∑ i ∈ Finset.range 119, stT152 (i+1)) + stT152 120 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 119
    simpa using h
  have hprev := st152_p119
  have hstep := st152_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p121 : ((10151014913541/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT152 (i+1))
      = (∑ i ∈ Finset.range 120, stT152 (i+1)) + stT152 121 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 120
    simpa using h
  have hprev := st152_p120
  have hstep := st152_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p122 : ((396753361749/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT152 (i+1))
      = (∑ i ∈ Finset.range 121, stT152 (i+1)) + stT152 122 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 121
    simpa using h
  have hprev := st152_p121
  have hstep := st152_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p123 : ((1895548678283/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT152 (i+1))
      = (∑ i ∈ Finset.range 122, stT152 (i+1)) + stT152 123 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 122
    simpa using h
  have hprev := st152_p122
  have hstep := st152_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p124 : ((1177356235341/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT152 (i+1))
      = (∑ i ∈ Finset.range 123, stT152 (i+1)) + stT152 124 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 123
    simpa using h
  have hprev := st152_p123
  have hstep := st152_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p125 : ((19630431309983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT152 (i+1))
      = (∑ i ∈ Finset.range 124, stT152 (i+1)) + stT152 125 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 124
    simpa using h
  have hprev := st152_p124
  have hstep := st152_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p126 : ((20294374449233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT152 (i+1))
      = (∑ i ∈ Finset.range 125, stT152 (i+1)) + stT152 126 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 125
    simpa using h
  have hprev := st152_p125
  have hstep := st152_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p127 : ((4995319629499/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT152 (i+1))
      = (∑ i ∈ Finset.range 126, stT152 (i+1)) + stT152 127 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 126
    simpa using h
  have hprev := st152_p126
  have hstep := st152_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p128 : ((2387186799611/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT152 (i+1))
      = (∑ i ∈ Finset.range 127, stT152 (i+1)) + stT152 128 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 127
    simpa using h
  have hprev := st152_p127
  have hstep := st152_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p129 : ((18749743545869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT152 (i+1))
      = (∑ i ∈ Finset.range 128, stT152 (i+1)) + stT152 129 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 128
    simpa using h
  have hprev := st152_p128
  have hstep := st152_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p130 : ((19358841031593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT152 (i+1))
      = (∑ i ∈ Finset.range 129, stT152 (i+1)) + stT152 130 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 129
    simpa using h
  have hprev := st152_p129
  have hstep := st152_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p131 : ((20175960465737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT152 (i+1))
      = (∑ i ∈ Finset.range 130, stT152 (i+1)) + stT152 131 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 130
    simpa using h
  have hprev := st152_p130
  have hstep := st152_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p132 : ((20222171975821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT152 (i+1))
      = (∑ i ∈ Finset.range 131, stT152 (i+1)) + stT152 132 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 131
    simpa using h
  have hprev := st152_p131
  have hstep := st152_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p133 : ((19451724797291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT152 (i+1))
      = (∑ i ∈ Finset.range 132, stT152 (i+1)) + stT152 133 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 132
    simpa using h
  have hprev := st152_p132
  have hstep := st152_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p134 : ((3754036106591/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT152 (i+1))
      = (∑ i ∈ Finset.range 133, stT152 (i+1)) + stT152 134 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 133
    simpa using h
  have hprev := st152_p133
  have hstep := st152_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p135 : ((18958887561751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT152 (i+1))
      = (∑ i ∈ Finset.range 134, stT152 (i+1)) + stT152 135 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 134
    simpa using h
  have hprev := st152_p134
  have hstep := st152_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p136 : ((19794161086539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT152 (i+1))
      = (∑ i ∈ Finset.range 135, stT152 (i+1)) + stT152 136 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 135
    simpa using h
  have hprev := st152_p135
  have hstep := st152_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p137 : ((20334743517291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT152 (i+1))
      = (∑ i ∈ Finset.range 136, stT152 (i+1)) + stT152 137 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 136
    simpa using h
  have hprev := st152_p136
  have hstep := st152_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p138 : ((9993677449709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT152 (i+1))
      = (∑ i ∈ Finset.range 137, stT152 (i+1)) + stT152 138 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 137
    simpa using h
  have hprev := st152_p137
  have hstep := st152_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p139 : ((4785078586831/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT152 (i+1))
      = (∑ i ∈ Finset.range 138, stT152 (i+1)) + stT152 139 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 138
    simpa using h
  have hprev := st152_p138
  have hstep := st152_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p140 : ((9354983246127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT152 (i+1))
      = (∑ i ∈ Finset.range 139, stT152 (i+1)) + stT152 140 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 139
    simpa using h
  have hprev := st152_p139
  have hstep := st152_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p141 : ((1914842062029/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT152 (i+1))
      = (∑ i ∈ Finset.range 140, stT152 (i+1)) + stT152 141 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 140
    simpa using h
  have hprev := st152_p140
  have hstep := st152_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p142 : ((156144260697/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT152 (i+1))
      = (∑ i ∈ Finset.range 141, stT152 (i+1)) + stT152 142 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 141
    simpa using h
  have hprev := st152_p141
  have hstep := st152_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p143 : ((5088113342613/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT152 (i+1))
      = (∑ i ∈ Finset.range 142, stT152 (i+1)) + stT152 143 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 142
    simpa using h
  have hprev := st152_p142
  have hstep := st152_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p144 : ((9938817745299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT152 (i+1))
      = (∑ i ∈ Finset.range 143, stT152 (i+1)) + stT152 144 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 143
    simpa using h
  have hprev := st152_p143
  have hstep := st152_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p145 : ((2381287667561/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT152 (i+1))
      = (∑ i ∈ Finset.range 144, stT152 (i+1)) + stT152 145 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 144
    simpa using h
  have hprev := st152_p144
  have hstep := st152_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p146 : ((9349317913287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT152 (i+1))
      = (∑ i ∈ Finset.range 145, stT152 (i+1)) + stT152 146 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 145
    simpa using h
  have hprev := st152_p145
  have hstep := st152_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p147 : ((1916343242987/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT152 (i+1))
      = (∑ i ∈ Finset.range 146, stT152 (i+1)) + stT152 147 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 146
    simpa using h
  have hprev := st152_p146
  have hstep := st152_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p148 : ((4995995546603/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT152 (i+1))
      = (∑ i ∈ Finset.range 147, stT152 (i+1)) + stT152 148 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 147
    simpa using h
  have hprev := st152_p147
  have hstep := st152_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p149 : ((20368607044757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT152 (i+1))
      = (∑ i ∈ Finset.range 148, stT152 (i+1)) + stT152 149 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 148
    simpa using h
  have hprev := st152_p148
  have hstep := st152_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p150 : ((9978626703333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT152 (i+1))
      = (∑ i ∈ Finset.range 149, stT152 (i+1)) + stT152 150 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 149
    simpa using h
  have hprev := st152_p149
  have hstep := st152_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p151 : ((4785965790819/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT152 (i+1))
      = (∑ i ∈ Finset.range 150, stT152 (i+1)) + stT152 151 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 150
    simpa using h
  have hprev := st152_p150
  have hstep := st152_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p152 : ((4671397191373/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT152 (i+1))
      = (∑ i ∈ Finset.range 151, stT152 (i+1)) + stT152 152 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 151
    simpa using h
  have hprev := st152_p151
  have hstep := st152_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p153 : ((474941462839/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT152 (i+1))
      = (∑ i ∈ Finset.range 152, stT152 (i+1)) + stT152 153 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 152
    simpa using h
  have hprev := st152_p152
  have hstep := st152_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p154 : ((2473725915733/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT152 (i+1))
      = (∑ i ∈ Finset.range 153, stT152 (i+1)) + stT152 154 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 153
    simpa using h
  have hprev := st152_p153
  have hstep := st152_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p155 : ((2034959795641/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT152 (i+1))
      = (∑ i ∈ Finset.range 154, stT152 (i+1)) + stT152 155 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 154
    simpa using h
  have hprev := st152_p154
  have hstep := st152_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p156 : ((20185544213587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT152 (i+1))
      = (∑ i ∈ Finset.range 155, stT152 (i+1)) + stT152 156 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 155
    simpa using h
  have hprev := st152_p155
  have hstep := st152_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p157 : ((2431041412439/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT152 (i+1))
      = (∑ i ∈ Finset.range 156, stT152 (i+1)) + stT152 157 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 156
    simpa using h
  have hprev := st152_p156
  have hstep := st152_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p158 : ((938965180859/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT152 (i+1))
      = (∑ i ∈ Finset.range 157, stT152 (i+1)) + stT152 158 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 157
    simpa using h
  have hprev := st152_p157
  have hstep := st152_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p159 : ((4686896970399/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT152 (i+1))
      = (∑ i ∈ Finset.range 158, stT152 (i+1)) + stT152 159 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 158
    simpa using h
  have hprev := st152_p158
  have hstep := st152_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p160 : ((2421646431981/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT152 (i+1))
      = (∑ i ∈ Finset.range 159, stT152 (i+1)) + stT152 160 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 159
    simpa using h
  have hprev := st152_p159
  have hstep := st152_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p161 : ((10064249222089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT152 (i+1))
      = (∑ i ∈ Finset.range 160, stT152 (i+1)) + stT152 161 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 160
    simpa using h
  have hprev := st152_p160
  have hstep := st152_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p162 : ((254884091943/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT152 (i+1))
      = (∑ i ∈ Finset.range 161, stT152 (i+1)) + stT152 162 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 161
    simpa using h
  have hprev := st152_p161
  have hstep := st152_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p163 : ((9975816402681/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT152 (i+1))
      = (∑ i ∈ Finset.range 162, stT152 (i+1)) + stT152 163 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 162
    simpa using h
  have hprev := st152_p162
  have hstep := st152_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p164 : ((1917155404479/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT152 (i+1))
      = (∑ i ∈ Finset.range 163, stT152 (i+1)) + stT152 164 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 163
    simpa using h
  have hprev := st152_p163
  have hstep := st152_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p165 : ((145892557239/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT152 (i+1))
      = (∑ i ∈ Finset.range 164, stT152 (i+1)) + stT152 165 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 164
    simpa using h
  have hprev := st152_p164
  have hstep := st152_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p166 : ((9423896069071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT152 (i+1))
      = (∑ i ∈ Finset.range 165, stT152 (i+1)) + stT152 166 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 165
    simpa using h
  have hprev := st152_p165
  have hstep := st152_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p167 : ((9775191591673/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT152 (i+1))
      = (∑ i ∈ Finset.range 166, stT152 (i+1)) + stT152 167 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 166
    simpa using h
  have hprev := st152_p166
  have hstep := st152_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p168 : ((2023639900871/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT152 (i+1))
      = (∑ i ∈ Finset.range 167, stT152 (i+1)) + stT152 168 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 167
    simpa using h
  have hprev := st152_p167
  have hstep := st152_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p169 : ((2038432963001/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT152 (i+1))
      = (∑ i ∈ Finset.range 168, stT152 (i+1)) + stT152 169 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 168
    simpa using h
  have hprev := st152_p168
  have hstep := st152_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p170 : ((3977666212723/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT152 (i+1))
      = (∑ i ∈ Finset.range 169, stT152 (i+1)) + stT152 170 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 169
    simpa using h
  have hprev := st152_p169
  have hstep := st152_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p171 : ((3824758154563/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT152 (i+1))
      = (∑ i ∈ Finset.range 170, stT152 (i+1)) + stT152 171 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 170
    simpa using h
  have hprev := st152_p170
  have hstep := st152_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p172 : ((2331985772609/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT152 (i+1))
      = (∑ i ∈ Finset.range 171, stT152 (i+1)) + stT152 172 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 171
    simpa using h
  have hprev := st152_p171
  have hstep := st152_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p173 : ((18822170394077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT152 (i+1))
      = (∑ i ∈ Finset.range 172, stT152 (i+1)) + stT152 173 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 172
    simpa using h
  have hprev := st152_p172
  have hstep := st152_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p174 : ((19496591811131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT152 (i+1))
      = (∑ i ∈ Finset.range 173, stT152 (i+1)) + stT152 174 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 173
    simpa using h
  have hprev := st152_p173
  have hstep := st152_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p175 : ((20193719195723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT152 (i+1))
      = (∑ i ∈ Finset.range 174, stT152 (i+1)) + stT152 175 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 174
    simpa using h
  have hprev := st152_p174
  have hstep := st152_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p176 : ((4084409820963/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT152 (i+1))
      = (∑ i ∈ Finset.range 175, stT152 (i+1)) + stT152 176 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 175
    simpa using h
  have hprev := st152_p175
  have hstep := st152_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p177 : ((1251684914829/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT152 (i+1))
      = (∑ i ∈ Finset.range 176, stT152 (i+1)) + stT152 177 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 176
    simpa using h
  have hprev := st152_p176
  have hstep := st152_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p178 : ((602721550119/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT152 (i+1))
      = (∑ i ∈ Finset.range 177, stT152 (i+1)) + stT152 178 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 177
    simpa using h
  have hprev := st152_p177
  have hstep := st152_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p179 : ((935541457711/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT152 (i+1))
      = (∑ i ∈ Finset.range 178, stT152 (i+1)) + stT152 179 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 178
    simpa using h
  have hprev := st152_p178
  have hstep := st152_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p180 : ((1167863577683/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT152 (i+1))
      = (∑ i ∈ Finset.range 179, stT152 (i+1)) + stT152 180 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 179
    simpa using h
  have hprev := st152_p179
  have hstep := st152_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p181 : ((9611709375507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT152 (i+1))
      = (∑ i ∈ Finset.range 180, stT152 (i+1)) + stT152 181 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 180
    simpa using h
  have hprev := st152_p180
  have hstep := st152_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p182 : ((3992506442529/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT152 (i+1))
      = (∑ i ∈ Finset.range 181, stT152 (i+1)) + stT152 182 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 181
    simpa using h
  have hprev := st152_p181
  have hstep := st152_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p183 : ((4083454280601/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT152 (i+1))
      = (∑ i ∈ Finset.range 182, stT152 (i+1)) + stT152 183 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 182
    simpa using h
  have hprev := st152_p182
  have hstep := st152_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p184 : ((4059129299441/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT152 (i+1))
      = (∑ i ∈ Finset.range 183, stT152 (i+1)) + stT152 184 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 183
    simpa using h
  have hprev := st152_p183
  have hstep := st152_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p185 : ((1968113541983/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT152 (i+1))
      = (∑ i ∈ Finset.range 184, stT152 (i+1)) + stT152 185 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 184
    simpa using h
  have hprev := st152_p184
  have hstep := st152_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p186 : ((9484278438829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT152 (i+1))
      = (∑ i ∈ Finset.range 185, stT152 (i+1)) + stT152 186 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 185
    simpa using h
  have hprev := st152_p185
  have hstep := st152_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p187 : ((9303336635347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT152 (i+1))
      = (∑ i ∈ Finset.range 186, stT152 (i+1)) + stT152 187 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 186
    simpa using h
  have hprev := st152_p186
  have hstep := st152_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p188 : ((9408655032229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT152 (i+1))
      = (∑ i ∈ Finset.range 187, stT152 (i+1)) + stT152 188 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 187
    simpa using h
  have hprev := st152_p187
  have hstep := st152_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p189 : ((9732668161669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT152 (i+1))
      = (∑ i ∈ Finset.range 188, stT152 (i+1)) + stT152 189 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 188
    simpa using h
  have hprev := st152_p188
  have hstep := st152_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p190 : ((10075730889811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT152 (i+1))
      = (∑ i ∈ Finset.range 189, stT152 (i+1)) + stT152 190 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 189
    simpa using h
  have hprev := st152_p189
  have hstep := st152_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p191 : ((10230521457761/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT152 (i+1))
      = (∑ i ∈ Finset.range 190, stT152 (i+1)) + stT152 191 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 190
    simpa using h
  have hprev := st152_p190
  have hstep := st152_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p192 : ((2021248346469/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT152 (i+1))
      = (∑ i ∈ Finset.range 191, stT152 (i+1)) + stT152 192 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 191
    simpa using h
  have hprev := st152_p191
  have hstep := st152_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p193 : ((9779023456169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT152 (i+1))
      = (∑ i ∈ Finset.range 192, stT152 (i+1)) + stT152 193 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 192
    simpa using h
  have hprev := st152_p192
  have hstep := st152_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p194 : ((9442523252459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT152 (i+1))
      = (∑ i ∈ Finset.range 193, stT152 (i+1)) + stT152 194 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 193
    simpa using h
  have hprev := st152_p193
  have hstep := st152_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p195 : ((18584276056573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT152 (i+1))
      = (∑ i ∈ Finset.range 194, stT152 (i+1)) + stT152 195 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 194
    simpa using h
  have hprev := st152_p194
  have hstep := st152_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p196 : ((9412602550679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT152 (i+1))
      = (∑ i ∈ Finset.range 195, stT152 (i+1)) + stT152 196 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 195
    simpa using h
  have hprev := st152_p195
  have hstep := st152_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p197 : ((9732865652849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT152 (i+1))
      = (∑ i ∈ Finset.range 196, stT152 (i+1)) + stT152 197 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 196
    simpa using h
  have hprev := st152_p196
  have hstep := st152_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p198 : ((5035268237427/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT152 (i+1))
      = (∑ i ∈ Finset.range 197, stT152 (i+1)) + stT152 198 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 197
    simpa using h
  have hprev := st152_p197
  have hstep := st152_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p199 : ((20473767107271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT152 (i+1))
      = (∑ i ∈ Finset.range 198, stT152 (i+1)) + stT152 199 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 198
    simpa using h
  have hprev := st152_p198
  have hstep := st152_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p200 : ((10141431533259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT152 (i+1))
      = (∑ i ∈ Finset.range 199, stT152 (i+1)) + stT152 200 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 199
    simpa using h
  have hprev := st152_p199
  have hstep := st152_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p201 : ((2459701854177/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT152 (i+1))
      = (∑ i ∈ Finset.range 200, stT152 (i+1)) + stT152 201 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 200
    simpa using h
  have hprev := st152_p200
  have hstep := st152_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p202 : ((9495088184341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT152 (i+1))
      = (∑ i ∈ Finset.range 201, stT152 (i+1)) + stT152 202 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 201
    simpa using h
  have hprev := st152_p201
  have hstep := st152_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p203 : ((1161926809701/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT152 (i+1))
      = (∑ i ∈ Finset.range 202, stT152 (i+1)) + stT152 203 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 202
    simpa using h
  have hprev := st152_p202
  have hstep := st152_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p204 : ((2336210915367/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT152 (i+1))
      = (∑ i ∈ Finset.range 203, stT152 (i+1)) + stT152 204 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 203
    simpa using h
  have hprev := st152_p203
  have hstep := st152_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p205 : ((4807544638329/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT152 (i+1))
      = (∑ i ∈ Finset.range 204, stT152 (i+1)) + stT152 205 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 204
    simpa using h
  have hprev := st152_p204
  have hstep := st152_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p206 : ((19925865757083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT152 (i+1))
      = (∑ i ∈ Finset.range 205, stT152 (i+1)) + stT152 206 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 205
    simpa using h
  have hprev := st152_p205
  have hstep := st152_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p207 : ((20415065561211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT152 (i+1))
      = (∑ i ∈ Finset.range 206, stT152 (i+1)) + stT152 207 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 206
    simpa using h
  have hprev := st152_p206
  have hstep := st152_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p208 : ((159754074987/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT152 (i+1))
      = (∑ i ∈ Finset.range 207, stT152 (i+1)) + stT152 208 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 207
    simpa using h
  have hprev := st152_p207
  have hstep := st152_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p209 : ((20013163786201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT152 (i+1))
      = (∑ i ∈ Finset.range 208, stT152 (i+1)) + stT152 209 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 208
    simpa using h
  have hprev := st152_p208
  have hstep := st152_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p210 : ((19332384694429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT152 (i+1))
      = (∑ i ∈ Finset.range 209, stT152 (i+1)) + stT152 210 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 209
    simpa using h
  have hprev := st152_p209
  have hstep := st152_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p211 : ((18748176960739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT152 (i+1))
      = (∑ i ∈ Finset.range 210, stT152 (i+1)) + stT152 211 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 210
    simpa using h
  have hprev := st152_p210
  have hstep := st152_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p212 : ((463718354429/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT152 (i+1))
      = (∑ i ∈ Finset.range 211, stT152 (i+1)) + stT152 212 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 211
    simpa using h
  have hprev := st152_p211
  have hstep := st152_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p213 : ((470713438721/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT152 (i+1))
      = (∑ i ∈ Finset.range 212, stT152 (i+1)) + stT152 213 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 212
    simpa using h
  have hprev := st152_p212
  have hstep := st152_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p214 : ((2430940129/1250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT152 (i+1))
      = (∑ i ∈ Finset.range 213, stT152 (i+1)) + stT152 214 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 213
    simpa using h
  have hprev := st152_p213
  have hstep := st152_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p215 : ((1005234181523/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT152 (i+1))
      = (∑ i ∈ Finset.range 214, stT152 (i+1)) + stT152 215 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 214
    simpa using h
  have hprev := st152_p214
  have hstep := st152_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p216 : ((20486006807637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT152 (i+1))
      = (∑ i ∈ Finset.range 215, stT152 (i+1)) + stT152 216 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 215
    simpa using h
  have hprev := st152_p215
  have hstep := st152_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p217 : ((20413401619507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT152 (i+1))
      = (∑ i ∈ Finset.range 216, stT152 (i+1)) + stT152 217 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 216
    simpa using h
  have hprev := st152_p216
  have hstep := st152_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p218 : ((19924709292637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT152 (i+1))
      = (∑ i ∈ Finset.range 217, stT152 (i+1)) + stT152 218 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 217
    simpa using h
  have hprev := st152_p217
  have hstep := st152_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p219 : ((19250553871033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT152 (i+1))
      = (∑ i ∈ Finset.range 218, stT152 (i+1)) + stT152 219 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 218
    simpa using h
  have hprev := st152_p218
  have hstep := st152_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p220 : ((18703100100033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT152 (i+1))
      = (∑ i ∈ Finset.range 219, stT152 (i+1)) + stT152 220 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 219
    simpa using h
  have hprev := st152_p219
  have hstep := st152_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p221 : ((9265671569789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT152 (i+1))
      = (∑ i ∈ Finset.range 220, stT152 (i+1)) + stT152 221 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 220
    simpa using h
  have hprev := st152_p220
  have hstep := st152_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p222 : ((9404960265827/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT152 (i+1))
      = (∑ i ∈ Finset.range 221, stT152 (i+1)) + stT152 222 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 221
    simpa using h
  have hprev := st152_p221
  have hstep := st152_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p223 : ((19410055277911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT152 (i+1))
      = (∑ i ∈ Finset.range 222, stT152 (i+1)) + stT152 223 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 222
    simpa using h
  have hprev := st152_p222
  have hstep := st152_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p224 : ((1003099710453/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT152 (i+1))
      = (∑ i ∈ Finset.range 223, stT152 (i+1)) + stT152 224 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 223
    simpa using h
  have hprev := st152_p223
  have hstep := st152_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p225 : ((2047762379343/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT152 (i+1))
      = (∑ i ∈ Finset.range 224, stT152 (i+1)) + stT152 225 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 224
    simpa using h
  have hprev := st152_p224
  have hstep := st152_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p226 : ((10238513891147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT152 (i+1))
      = (∑ i ∈ Finset.range 225, stT152 (i+1)) + stT152 226 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 225
    simpa using h
  have hprev := st152_p225
  have hstep := st152_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p227 : ((2006382574237/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT152 (i+1))
      = (∑ i ∈ Finset.range 226, stT152 (i+1)) + stT152 227 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 226
    simpa using h
  have hprev := st152_p226
  have hstep := st152_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p228 : ((19419076366787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT152 (i+1))
      = (∑ i ∈ Finset.range 227, stT152 (i+1)) + stT152 228 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 227
    simpa using h
  have hprev := st152_p227
  have hstep := st152_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p229 : ((3763924468153/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT152 (i+1))
      = (∑ i ∈ Finset.range 228, stT152 (i+1)) + stT152 229 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 228
    simpa using h
  have hprev := st152_p228
  have hstep := st152_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p230 : ((9259306468061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT152 (i+1))
      = (∑ i ∈ Finset.range 229, stT152 (i+1)) + stT152 230 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 229
    simpa using h
  have hprev := st152_p229
  have hstep := st152_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p231 : ((18639887122393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT152 (i+1))
      = (∑ i ∈ Finset.range 230, stT152 (i+1)) + stT152 231 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 230
    simpa using h
  have hprev := st152_p230
  have hstep := st152_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p232 : ((19129616663281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT152 (i+1))
      = (∑ i ∈ Finset.range 231, stT152 (i+1)) + stT152 232 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 231
    simpa using h
  have hprev := st152_p231
  have hstep := st152_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p233 : ((9891431025929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT152 (i+1))
      = (∑ i ∈ Finset.range 232, stT152 (i+1)) + stT152 233 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 232
    simpa using h
  have hprev := st152_p232
  have hstep := st152_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p234 : ((10165543666569/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT152 (i+1))
      = (∑ i ∈ Finset.range 233, stT152 (i+1)) + stT152 234 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 233
    simpa using h
  have hprev := st152_p233
  have hstep := st152_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p235 : ((411053715281/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT152 (i+1))
      = (∑ i ∈ Finset.range 234, stT152 (i+1)) + stT152 235 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 234
    simpa using h
  have hprev := st152_p234
  have hstep := st152_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p236 : ((4072208599887/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT152 (i+1))
      = (∑ i ∈ Finset.range 235, stT152 (i+1)) + stT152 236 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 235
    simpa using h
  have hprev := st152_p235
  have hstep := st152_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p237 : ((3967175469339/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT152 (i+1))
      = (∑ i ∈ Finset.range 236, stT152 (i+1)) + stT152 237 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 236
    simpa using h
  have hprev := st152_p236
  have hstep := st152_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p238 : ((19187677884123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT152 (i+1))
      = (∑ i ∈ Finset.range 237, stT152 (i+1)) + stT152 238 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 237
    simpa using h
  have hprev := st152_p237
  have hstep := st152_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p239 : ((18671920897143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT152 (i+1))
      = (∑ i ∈ Finset.range 238, stT152 (i+1)) + stT152 239 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 238
    simpa using h
  have hprev := st152_p238
  have hstep := st152_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p240 : ((3697692653013/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT152 (i+1))
      = (∑ i ∈ Finset.range 239, stT152 (i+1)) + stT152 240 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 239
    simpa using h
  have hprev := st152_p239
  have hstep := st152_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p241 : ((18705606320197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT152 (i+1))
      = (∑ i ∈ Finset.range 240, stT152 (i+1)) + stT152 241 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 240
    simpa using h
  have hprev := st152_p240
  have hstep := st152_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p242 : ((19237021849933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT152 (i+1))
      = (∑ i ∈ Finset.range 241, stT152 (i+1)) + stT152 242 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 241
    simpa using h
  have hprev := st152_p241
  have hstep := st152_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p243 : ((19878214571433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT152 (i+1))
      = (∑ i ∈ Finset.range 242, stT152 (i+1)) + stT152 243 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 242
    simpa using h
  have hprev := st152_p242
  have hstep := st152_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p244 : ((20386453448113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT152 (i+1))
      = (∑ i ∈ Finset.range 243, stT152 (i+1)) + stT152 244 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 243
    simpa using h
  have hprev := st152_p243
  have hstep := st152_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p245 : ((164580269997/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT152 (i+1))
      = (∑ i ∈ Finset.range 244, stT152 (i+1)) + stT152 245 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 244
    simpa using h
  have hprev := st152_p244
  have hstep := st152_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p246 : ((20369793189703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT152 (i+1))
      = (∑ i ∈ Finset.range 245, stT152 (i+1)) + stT152 246 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 245
    simpa using h
  have hprev := st152_p245
  have hstep := st152_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p247 : ((9927927489179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT152 (i+1))
      = (∑ i ∈ Finset.range 246, stT152 (i+1)) + stT152 247 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 246
    simpa using h
  have hprev := st152_p246
  have hstep := st152_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p248 : ((4805227147111/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT152 (i+1))
      = (∑ i ∈ Finset.range 247, stT152 (i+1)) + stT152 248 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 247
    simpa using h
  have hprev := st152_p247
  have hstep := st152_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p249 : ((9348063626597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT152 (i+1))
      = (∑ i ∈ Finset.range 248, stT152 (i+1)) + stT152 249 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 248
    simpa using h
  have hprev := st152_p248
  have hstep := st152_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_p250 : ((9234765142529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT152 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT152 (i+1))
      = (∑ i ∈ Finset.range 249, stT152 (i+1)) + stT152 250 := by
    have h := Finset.sum_range_succ (fun i => stT152 (i+1)) 249
    simpa using h
  have hprev := st152_p249
  have hstep := st152_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st152_s250 :
    |Real.sin (((152 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))
      - ((-933633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -2421461/5000000) (δ := 7639/1000000000) (ψ := -373799/500000) 152 134
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 152`** (evaluated boundary). -/
theorem station_152_sign : hardyG ((((152:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 152 250 (by norm_num) (by norm_num)
    ((-373799/500000 : ℚ) : ℝ)
  have hchain := st152_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT152 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((152 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-373799/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st152_c250
  have hsinb := abs_le.mp st152_s250
  have hbdy_lo : ((35944620237783/369668000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((152 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-373799/500000 : ℚ) : ℝ))) / 2
          - ((((152:ℕ)):ℝ))
            * Real.sin (((152 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-373799/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((152:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((152:ℝ) * Real.log (250:ℝ) - ((-373799/500000 : ℚ) : ℝ))) / 2
        - ((152:ℝ)) * Real.sin ((152:ℝ) * Real.log (250:ℝ) - ((-373799/500000 : ℚ) : ℝ))
        ≥ ((284167413/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((152:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((284167413/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((284167413/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((284167413/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((152:ℕ)):ℝ))+1) * (((((152:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((166041915017/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((9234765142529/5000000000000 : ℚ) : ℝ) + ((35944620237783/369668000000000 : ℚ) : ℝ)
      - ((166041915017/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-373799/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((152:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-373799/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((152:ℕ)):ℝ)))).re
      - Real.sin ((-373799/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((152:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((152:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((152:ℕ)):ℝ))
      = (((((152:ℕ)):ℝ)) * (Real.log ((((152:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((152:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_152
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
  have hθwin : |(((-373799/500000 : ℚ) : ℝ) + ((27:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((152:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((152:ℕ)):ℝ)))
    (φ := ((-373799/500000 : ℚ) : ℝ) + ((27:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-373799/500000 : ℚ) : ℝ) + ((27:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-373799/500000 : ℚ)) : ℝ) - Real.pi) + ((27:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-373799/500000 : ℚ)) : ℝ) - Real.pi) 27).1,
    (cos_sin_shift ((((-373799/500000 : ℚ)) : ℝ) - Real.pi) 27).2]
  exact cos_sin_flip ((-373799/500000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_152_sign
end AxiomAudit
