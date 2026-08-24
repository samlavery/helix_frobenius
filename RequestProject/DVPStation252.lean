import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 252` (rung-262.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT252 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((252 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-267951/500000 : ℚ) : ℝ))

theorem st252_c1 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((26869/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 267951/2000000) (δ := 1/1000000000) (ψ := -267951/500000) 252 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t1 : ((429879/500000 : ℚ) : ℝ) ≤ stT252 1 := by
  have hc : ((429879/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((429879/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((429879/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c2 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((751671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28133/156250) (δ := 12603/1000000000) (ψ := -267951/500000) 252 28
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t2 : ((5314762449607/10000000000000 : ℚ) : ℝ) ≤ stT252 2 := by
  have hc : ((751621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5314762449607/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((751621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c3 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((601007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2315089/10000000) (δ := 12717/1000000000) (ψ := -267951/500000) 252 44
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t3 : ((1734813220707/5000000000000 : ℚ) : ℝ) ≤ stT252 3 := by
  have hc : ((600957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1734813220707/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((600957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c4 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-394481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1235187/2500000) (δ := 12799/1000000000) (ψ := -267951/500000) 252 56
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t4 : ((-1972655394531/10000000000000 : ℚ) : ℝ) ≤ stT252 4 := by
  have hc : ((-394531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1972655394531/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-394531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c5 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-330437/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5731949/10000000) (δ := 2527/200000000) (ψ := -267951/500000) 252 65
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t5 : ((-92366937927/312500000000 : ℚ) : ℝ) ≤ stT252 5 := by
  have hc : ((-165231/250000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92366937927/312500000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-165231/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c6 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((946023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -825147/10000000) (δ := 2537/200000000) (ψ := -267951/500000) 252 72
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t6 : ((1930958872493/5000000000000 : ℚ) : ℝ) ≤ stT252 6 := by
  have hc : ((945973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1930958872493/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((945973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c7 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((684553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 408403/2000000) (δ := 6381/500000000) (ψ := -267951/500000) 252 78
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t7 : ((646794414233/2500000000000 : ℚ) : ℝ) ≤ stT252 7 := by
  have hc : ((684503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((646794414233/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((684503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c8 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-24897/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 381349/500000) (δ := 6353/500000000) (ψ := -267951/500000) 252 83
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t8 : ((-176057218831/500000000000 : ℚ) : ℝ) ≤ stT252 8 := by
  have hc : ((-99593/100000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176057218831/500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-99593/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c9 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((251873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1645227/5000000) (δ := 12633/1000000000) (ψ := -267951/500000) 252 88
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t9 : ((839409916059/10000000000000 : ℚ) : ℝ) ≤ stT252 9 := by
  have hc : ((251823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((839409916059/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((251823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c10 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-918191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1708929/2500000) (δ := 6331/500000000) (ψ := -267951/500000) 252 92
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t10 : ((-1451866656499/5000000000000 : ℚ) : ℝ) ≤ stT252 10 := by
  have hc : ((-918241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1451866656499/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-918241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c11 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-489/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4049289/10000000) (δ := 12691/1000000000) (ψ := -267951/500000) 252 96
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t11 : ((-1475898303/100000000000 : ℚ) : ℝ) ≤ stT252 11 := by
  have hc : ((-979/20000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1475898303/100000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-979/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c12 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-3839/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1982691/5000000) (δ := 12719/1000000000) (ψ := -267951/500000) 252 100
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t12 : ((-694895333/156250000000 : ℚ) : ℝ) ≤ stT252 12 := by
  have hc : ((-7703/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-694895333/156250000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-7703/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c13 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((482553/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -662371/10000000) (δ := 12641/1000000000) (ψ := -267951/500000) 252 103
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t13 : ((83643213/312500000 : ℚ) : ℝ) ≤ stT252 13 := by
  have hc : ((15079/15625 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83643213/312500000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((15079/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c14 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((181011/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1098221/10000000) (δ := 79/6250000) (ψ := -267951/500000) 252 106
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t14 : ((120936361153/500000000000 : ℚ) : ℝ) ≤ stT252 14 := by
  have hc : ((181001/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120936361153/500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((181001/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c15 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-325781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -594573/1250000) (δ := 12719/1000000000) (ψ := -267951/500000) 252 109
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t15 : ((-841292057859/10000000000000 : ℚ) : ℝ) ≤ stT252 15 := by
  have hc : ((-325831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-841292057859/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-325831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c16 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-55509/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 897349/2000000) (δ := 6349/500000000) (ψ := -267951/500000) 252 111
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t16 : ((-277607611043/5000000000000 : ℚ) : ℝ) ≤ stT252 16 := by
  have hc : ((-111043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277607611043/5000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-111043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c17 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-41039/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4443647/10000000) (δ := 631/50000000) (ψ := -267951/500000) 252 114
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t17 : ((-99558479493/2000000000000 : ℚ) : ℝ) ≤ stT252 17 := by
  have hc : ((-41049/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99558479493/2000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-41049/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c18 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((199639/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75109/5000000) (δ := 12769/1000000000) (ψ := -267951/500000) 252 116
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t18 : ((235264972419/1000000000000 : ℚ) : ℝ) ≤ stT252 18 := by
  have hc : ((199629/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235264972419/1000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((199629/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c19 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((13653/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 699157/2500000) (δ := 12649/1000000000) (ψ := -267951/500000) 252 118
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t19 : ((501096654411/5000000000000 : ℚ) : ℝ) ≤ stT252 19 := by
  have hc : ((218423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((501096654411/5000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((218423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c20 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((11559/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 92387/250000) (δ := 637/50000000) (ψ := -267951/500000) 252 120
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t20 : ((103330892137/5000000000000 : ℚ) : ℝ) ≤ stT252 20 := by
  have hc : ((46211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103330892137/5000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((46211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c21 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((35587/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 150869/500000) (δ := 12677/1000000000) (ψ := -267951/500000) 252 122
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t21 : ((19411564399/250000000000 : ℚ) : ℝ) ≤ stT252 21 := by
  have hc : ((17791/50000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19411564399/250000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((17791/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c22 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((186923/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 909053/10000000) (δ := 12711/1000000000) (ψ := -267951/500000) 252 124
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t22 : ((398499824391/2000000000000 : ℚ) : ℝ) ≤ stT252 22 := by
  have hc : ((186913/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((398499824391/2000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((186913/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c23 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((134887/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2502239/10000000) (δ := 6353/500000000) (ψ := -267951/500000) 252 126
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t23 : ((70308188607/625000000000 : ℚ) : ℝ) ≤ stT252 23 := by
  have hc : ((269749/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70308188607/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((269749/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c24 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-95553/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3552809/5000000) (δ := 12683/1000000000) (ψ := -267951/500000) 252 128
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t24 : ((-48764250759/250000000000 : ℚ) : ℝ) ≤ stT252 24 := by
  have hc : ((-47779/50000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48764250759/250000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-47779/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c25 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((39777/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2904279/10000000) (δ := 3157/250000000) (ψ := -267951/500000) 252 129
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t25 : ((9943/125000 : ℚ) : ℝ) ≤ stT252 25 := by
  have hc : ((9943/25000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9943/125000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((9943/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c26 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((49733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3802607/10000000) (δ := 12761/1000000000) (ψ := -267951/500000) 252 131
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t26 : ((97436361963/10000000000000 : ℚ) : ℝ) ≤ stT252 26 := by
  have hc : ((49683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97436361963/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((49683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c27 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-135117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4265819/10000000) (δ := 6327/500000000) (ψ := -267951/500000) 252 132
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t27 : ((-260129026667/10000000000000 : ℚ) : ℝ) ≤ stT252 27 := by
  have hc : ((-135167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-260129026667/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-135167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c28 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-15533/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -529807/1250000) (δ := 3191/250000000) (ψ := -267951/500000) 252 134
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t28 : ((-117465728211/5000000000000 : ℚ) : ℝ) ≤ stT252 28 := by
  have hc : ((-62157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117465728211/5000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-62157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c29 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((649067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2161099/10000000) (δ := 3183/250000000) (ψ := -267951/500000) 252 135
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t29 : ((1205194065201/10000000000000 : ℚ) : ℝ) ≤ stT252 29 := by
  have hc : ((649017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1205194065201/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((649017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c30 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-999853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7811081/10000000) (δ := 101/8000000) (ψ := -267951/500000) 252 136
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t30 : ((-912782451513/5000000000000 : ℚ) : ℝ) ≤ stT252 30 := by
  have hc : ((-999903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-912782451513/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-999903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c31 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((381957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -368401/1250000) (δ := 1599/125000000) (ψ := -267951/500000) 252 138
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t31 : ((685925213071/10000000000000 : ℚ) : ℝ) ≤ stT252 31 := by
  have hc : ((381907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((685925213071/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((381907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c32 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((429213/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1346509/10000000) (δ := 397/31250000) (ψ := -267951/500000) 252 139
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t32 : ((94837994251/625000000000 : ℚ) : ℝ) ≤ stT252 32 := by
  have hc : ((107297/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94837994251/625000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((107297/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c33 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-212547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2512327/5000000) (δ := 12607/1000000000) (ψ := -267951/500000) 252 140
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t33 : ((-92510112111/1250000000000 : ℚ) : ℝ) ≤ stT252 33 := by
  have hc : ((-53143/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92510112111/1250000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-53143/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c34 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-994169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7583883/10000000) (δ := 6391/500000000) (ψ := -267951/500000) 252 142
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t34 : ((-852535832967/5000000000000 : ℚ) : ℝ) ≤ stT252 34 := by
  have hc : ((-994219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-852535832967/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-994219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c35 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-426927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5029721/10000000) (δ := 507/40000000) (ψ := -267951/500000) 252 143
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t35 : ((-721723065893/10000000000000 : ℚ) : ℝ) ≤ stT252 35 := by
  have hc : ((-426977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-721723065893/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-426977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c36 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((366077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2990017/10000000) (δ := 2527/200000000) (ψ := -267951/500000) 252 144
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t36 : ((305022377991/5000000000000 : ℚ) : ℝ) ≤ stT252 36 := by
  have hc : ((366027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((305022377991/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((366027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c37 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((419693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -143661/1000000) (δ := 12743/1000000000) (ψ := -267951/500000) 252 145
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t37 : ((172482393913/1250000000000 : ℚ) : ℝ) ≤ stT252 37 := by
  have hc : ((104917/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172482393913/1250000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((104917/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c38 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((99057/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42951/1250000) (δ := 12753/1000000000) (ψ := -267951/500000) 252 146
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t38 : ((20085442641/125000000000 : ℚ) : ℝ) ≤ stT252 38 := by
  have hc : ((24763/25000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20085442641/125000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((24763/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c39 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((992173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156497/5000000) (δ := 6323/500000000) (ψ := -267951/500000) 252 147
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t39 : ((1588667709563/10000000000000 : ℚ) : ℝ) ≤ stT252 39 := by
  have hc : ((992123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1588667709563/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((992123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c40 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((975437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 111049/2000000) (δ := 1583/125000000) (ψ := -267951/500000) 252 148
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t40 : ((771110725203/5000000000000 : ℚ) : ℝ) ≤ stT252 40 := by
  have hc : ((975387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((771110725203/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((975387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c41 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((246749/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 20181/500000) (δ := 12771/1000000000) (ψ := -267951/500000) 252 149
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t41 : ((770675042601/5000000000000 : ℚ) : ℝ) ≤ stT252 41 := by
  have hc : ((493473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((770675042601/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((493473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c42 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((998793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15357/1250000) (δ := 509/40000000) (ψ := -267951/500000) 252 150
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t42 : ((1541093407519/10000000000000 : ℚ) : ℝ) ≤ stT252 42 := by
  have hc : ((998743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1541093407519/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((998743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c43 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((920029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -251651/2500000) (δ := 12617/1000000000) (ψ := -267951/500000) 252 151
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t43 : ((280590835063/2000000000000 : ℚ) : ℝ) ≤ stT252 43 := by
  have hc : ((919979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((280590835063/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((919979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c44 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((627489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1115591/5000000) (δ := 12693/1000000000) (ψ := -267951/500000) 252 152
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t44 : ((236474857271/2500000000000 : ℚ) : ℝ) ≤ stT252 44 := by
  have hc : ((627439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((236474857271/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((627439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c45 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((58251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3781281/10000000) (δ := 1/78125) (ψ := -267951/500000) 252 153
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t45 : ((86760870911/10000000000000 : ℚ) : ℝ) ≤ stT252 45 := by
  have hc : ((58201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86760870911/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((58201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c46 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-39601/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2821269/5000000) (δ := 1587/125000000) (ψ := -267951/500000) 252 154
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t46 : ((-23357245593/250000000000 : ℚ) : ℝ) ≤ stT252 46 := by
  have hc : ((-316833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23357245593/250000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-316833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c47 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-49989/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1950383/2500000) (δ := 6307/500000000) (ψ := -267951/500000) 252 155
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t47 : ((-2916804059/20000000000 : ℚ) : ℝ) ≤ stT252 47 := by
  have hc : ((-99983/100000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2916804059/20000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-99983/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c48 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-28809/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 546211/1000000) (δ := 6307/500000000) (ψ := -267951/500000) 252 155
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t48 : ((-5198228453/62500000000 : ℚ) : ℝ) ≤ stT252 48 := by
  have hc : ((-57623/100000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5198228453/62500000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-57623/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c49 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((455647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2744243/10000000) (δ := 6361/500000000) (ψ := -267951/500000) 252 156
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t49 : ((650852661887/10000000000000 : ℚ) : ℝ) ≤ stT252 49 := by
  have hc : ((455597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((650852661887/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((455597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c50 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((995549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -235957/10000000) (δ := 6387/500000000) (ψ := -267951/500000) 252 157
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t50 : ((1407847627287/10000000000000 : ℚ) : ℝ) ≤ stT252 50 := by
  have hc : ((995499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1407847627287/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((995499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c51 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((22807/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1734141/5000000) (δ := 12667/1000000000) (ψ := -267951/500000) 252 158
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t51 : ((3192743421/125000000000 : ℚ) : ℝ) ≤ stT252 51 := by
  have hc : ((91203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3192743421/125000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((91203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c52 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-467159/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3471421/5000000) (δ := 12643/1000000000) (ψ := -267951/500000) 252 159
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t52 : ((-40491742449/312500000000 : ℚ) : ℝ) ≤ stT252 52 := by
  have hc : ((-29199/31250 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40491742449/312500000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-29199/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c53 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-436957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1264381/2500000) (δ := 12643/1000000000) (ψ := -267951/500000) 252 159
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t53 : ((-300137718621/5000000000000 : ℚ) : ℝ) ≤ stT252 53 := by
  have hc : ((-437007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-300137718621/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-437007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c54 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((180069/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 70349/625000) (δ := 51/4000000) (ψ := -267951/500000) 252 160
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t54 : ((245029148793/2000000000000 : ℚ) : ℝ) ≤ stT252 54 := by
  have hc : ((180059/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((245029148793/2000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((180059/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c55 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((14159/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3022447/10000000) (δ := 6373/500000000) (ψ := -267951/500000) 252 161
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t55 : ((19089284643/400000000000 : ℚ) : ℝ) ≤ stT252 55 := by
  have hc : ((14157/40000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19089284643/400000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((14157/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c56 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-981987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1475751/2000000) (δ := 6319/500000000) (ψ := -267951/500000) 252 162
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t56 : ((-1312302917359/10000000000000 : ℚ) : ℝ) ≤ stT252 56 := by
  have hc : ((-982037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1312302917359/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-982037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c57 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((61959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3771993/10000000) (δ := 6319/500000000) (ψ := -267951/500000) 252 162
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t57 : ((20500112897/2500000000000 : ℚ) : ℝ) ≤ stT252 57 := by
  have hc : ((61909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20500112897/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((61909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c58 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((924279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15299/156250) (δ := 99/7812500) (ψ := -267951/500000) 252 163
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t58 : ((151696478457/1250000000000 : ℚ) : ℝ) ≤ stT252 58 := by
  have hc : ((924229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151696478457/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((924229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c59 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-357371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5917627/10000000) (δ := 12779/1000000000) (ψ := -267951/500000) 252 164
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t59 : ((-11632256961/125000000000 : ℚ) : ℝ) ≤ stT252 59 := by
  have hc : ((-89349/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11632256961/125000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-89349/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c60 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-293171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2335423/5000000) (δ := 12779/1000000000) (ψ := -267951/500000) 252 164
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t60 : ((-75709368979/2000000000000 : ℚ) : ℝ) ≤ stT252 60 := by
  have hc : ((-293221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75709368979/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-293221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c61 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((193809/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -623659/10000000) (δ := 12717/1000000000) (ψ := -267951/500000) 252 165
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t61 : ((15508377377/125000000000 : ℚ) : ℝ) ≤ stT252 61 := by
  have hc : ((193799/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15508377377/125000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((193799/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c62 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-38029/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6087507/10000000) (δ := 1261/100000000) (ψ := -267951/500000) 252 166
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t62 : ((-48300081063/500000000000 : ℚ) : ℝ) ≤ stT252 62 := by
  have hc : ((-76063/100000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48300081063/500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-76063/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c63 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-26299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 798549/2000000) (δ := 1261/100000000) (ψ := -267951/500000) 252 166
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t63 : ((-16598315409/5000000000000 : ℚ) : ℝ) ≤ stT252 63 := by
  have hc : ((-26349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16598315409/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-26349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c64 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((376721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1793789/10000000) (δ := 127/10000000) (ψ := -267951/500000) 252 167
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t64 : ((47087/500000 : ℚ) : ℝ) ≤ stT252 64 := by
  have hc : ((47087/62500 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47087/500000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((47087/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c65 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-998851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7734107/10000000) (δ := 2559/200000000) (ψ := -267951/500000) 252 168
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t65 : ((-309746214387/2500000000000 : ℚ) : ℝ) ≤ stT252 65 := by
  have hc : ((-998901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-309746214387/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-998901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c66 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((182279/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 942209/5000000) (δ := 2559/200000000) (ψ := -267951/500000) 252 168
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t66 : ((224354386581/2500000000000 : ℚ) : ℝ) ≤ stT252 66 := by
  have hc : ((364533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224354386581/2500000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((364533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c67 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-168267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1087417/2500000) (δ := 793/62500000) (ψ := -267951/500000) 252 169
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t67 : ((-41126407463/2000000000000 : ℚ) : ℝ) ≤ stT252 67 := by
  have hc : ((-168317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41126407463/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-168317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c68 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-205131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 996769/2000000) (δ := 793/62500000) (ψ := -267951/500000) 252 169
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t68 : ((-62197093231/1250000000000 : ℚ) : ℝ) ≤ stT252 68 := by
  have hc : ((-51289/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62197093231/1250000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-51289/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c69 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((409609/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -763437/5000000) (δ := 6311/500000000) (ψ := -267951/500000) 252 170
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t69 : ((15408780471/156250000000 : ℚ) : ℝ) ≤ stT252 69 := by
  have hc : ((25599/31250 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15408780471/156250000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((25599/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c70 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-992023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7538007/10000000) (δ := 6311/500000000) (ψ := -267951/500000) 252 170
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t70 : ((-1185754419717/10000000000000 : ℚ) : ℝ) ≤ stT252 70 := by
  have hc : ((-992073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1185754419717/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-992073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c71 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((119173/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 383171/5000000) (δ := 12729/1000000000) (ψ := -267951/500000) 252 171
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t71 : ((565699338927/5000000000000 : ℚ) : ℝ) ≤ stT252 71 := by
  have hc : ((476667/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((565699338927/5000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((476667/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c72 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-77157/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6130253/10000000) (δ := 12767/1000000000) (ψ := -267951/500000) 252 172
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t72 : ((-2841760717/31250000000 : ℚ) : ℝ) ≤ stT252 72 := by
  have hc : ((-38581/50000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2841760717/31250000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-38581/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c73 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((104023/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1279763/5000000) (δ := 12767/1000000000) (ψ := -267951/500000) 252 172
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t73 : ((121737959343/2000000000000 : ℚ) : ℝ) ≤ stT252 73 := by
  have hc : ((104013/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121737959343/2000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((104013/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c74 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-257049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4576909/10000000) (δ := 12659/1000000000) (ψ := -267951/500000) 252 173
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t74 : ((-298871674223/10000000000000 : ℚ) : ℝ) ≤ stT252 74 := by
  have hc : ((-257099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-298871674223/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-257099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c75 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((9469/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 969911/2500000) (δ := 12659/1000000000) (ψ := -267951/500000) 252 173
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t75 : ((27262467/12500000000 : ℚ) : ℝ) ≤ stT252 75 := by
  have hc : ((2361/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27262467/12500000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((2361/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c76 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((44083/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3483843/10000000) (δ := 12651/1000000000) (ψ := -267951/500000) 252 174
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t76 : ((50552300999/2500000000000 : ℚ) : ℝ) ≤ stT252 76 := by
  have hc : ((88141/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50552300999/2500000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((88141/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c77 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-20243/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 237579/500000) (δ := 12651/1000000000) (ψ := -267951/500000) 252 174
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t77 : ((-92290422107/2500000000000 : ℚ) : ℝ) ≤ stT252 77 := by
  have hc : ((-161969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92290422107/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-161969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c78 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((425849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2827241/10000000) (δ := 6379/500000000) (ψ := -267951/500000) 252 175
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t78 : ((482122414323/10000000000000 : ℚ) : ℝ) ≤ stT252 78 := by
  have hc : ((425799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((482122414323/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((425799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c79 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-243449/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5198329/10000000) (δ := 6379/500000000) (ψ := -267951/500000) 252 175
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t79 : ((-4280151183/78125000000 : ℚ) : ℝ) ≤ stT252 79 := by
  have hc : ((-121737/250000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4280151183/78125000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-121737/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c80 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((511389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2584991/10000000) (δ := 6369/500000000) (ψ := -267951/500000) 252 176
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t80 : ((571693876187/10000000000000 : ℚ) : ℝ) ≤ stT252 80 := by
  have hc : ((511339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((571693876187/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((511339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c81 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-501799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 163787/312500) (δ := 6369/500000000) (ψ := -267951/500000) 252 176
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t81 : ((-69701305761/1250000000000 : ℚ) : ℝ) ≤ stT252 81 := by
  have hc : ((-501849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69701305761/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-501849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c82 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((458361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -342077/1250000) (δ := 12631/1000000000) (ψ := -267951/500000) 252 177
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t82 : ((101223942393/2000000000000 : ℚ) : ℝ) ≤ stT252 82 := by
  have hc : ((458311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101223942393/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((458311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c83 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-189701/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2449933/5000000) (δ := 12631/1000000000) (ψ := -267951/500000) 252 177
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t83 : ((-104125707909/2500000000000 : ℚ) : ℝ) ≤ stT252 83 := by
  have hc : ((-94863/250000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104125707909/2500000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-94863/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c84 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((262437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3263123/10000000) (δ := 6331/250000000) (ψ := -267951/500000) 252 178
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t84 : ((286287569443/10000000000000 : ℚ) : ℝ) ≤ stT252 84 := by
  have hc : ((262387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((286287569443/10000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((262387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c85 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-26509/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4192581/10000000) (δ := 12679/1000000000) (ψ := -267951/500000) 252 178
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t85 : ((-57533249079/5000000000000 : ℚ) : ℝ) ≤ stT252 85 := by
  have hc : ((-53043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57533249079/5000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-53043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c86 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-87851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2073451/5000000) (δ := 12787/1000000000) (ψ := -267951/500000) 252 179
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t86 : ((-11848263691/1250000000000 : ℚ) : ℝ) ≤ stT252 86 := by
  have hc : ((-87901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11848263691/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-87901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c87 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((310967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 627293/2000000) (δ := 12787/1000000000) (ψ := -267951/500000) 252 179
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t87 : ((20833615419/625000000000 : ℚ) : ℝ) ≤ stT252 87 := by
  have hc : ((310917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20833615419/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((310917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c88 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-273079/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2685709/5000000) (δ := 12709/1000000000) (ψ := -267951/500000) 252 180
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t88 : ((-4548905569/78125000000 : ℚ) : ℝ) ≤ stT252 88 := by
  have hc : ((-17069/31250 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4548905569/78125000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-17069/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c89 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((382773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1747267/10000000) (δ := 12709/1000000000) (ψ := -267951/500000) 252 180
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t89 : ((101427932939/1250000000000 : ℚ) : ℝ) ≤ stT252 89 := by
  have hc : ((95687/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101427932939/1250000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((95687/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c90 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-931243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6921517/10000000) (δ := 6301/500000000) (ψ := -267951/500000) 252 181
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t90 : ((-981669432249/10000000000000 : ℚ) : ℝ) ≤ stT252 90 := by
  have hc : ((-931293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-981669432249/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-931293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c91 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((999873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39889/10000000) (δ := 25401/1000000000) (ψ := -267951/500000) 252 181
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t91 : ((262024613433/2500000000000 : ℚ) : ℝ) ≤ stT252 91 := by
  have hc : ((999823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((262024613433/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((999823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c92 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-465889/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 692519/1000000) (δ := 6301/500000000) (ψ := -267951/500000) 252 181
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t92 : ((-242874678361/2500000000000 : ℚ) : ℝ) ≤ stT252 92 := by
  have hc : ((-232957/250000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242874678361/2500000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-232957/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c93 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((176181/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -985953/5000000) (δ := 3177/250000000) (ψ := -267951/500000) 252 182
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t93 : ((365356204487/5000000000000 : ℚ) : ℝ) ≤ stT252 93 := by
  have hc : ((352337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((365356204487/5000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((352337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c94 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-329389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4766133/10000000) (δ := 3177/250000000) (ψ := -267951/500000) 252 182
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t94 : ((-169895316129/5000000000000 : ℚ) : ℝ) ≤ stT252 94 := by
  have hc : ((-329439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169895316129/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-329439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c95 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-138797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1068777/2500000) (δ := 3197/250000000) (ψ := -267951/500000) 252 183
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t95 : ((-142454106213/10000000000000 : ℚ) : ℝ) ≤ stT252 95 := by
  have hc : ((-138847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142454106213/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-138847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c96 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((74857/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2321811/10000000) (δ := 3197/250000000) (ψ := -267951/500000) 252 183
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t96 : ((15278834493/250000000000 : ℚ) : ℝ) ≤ stT252 96 := by
  have hc : ((299403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15278834493/250000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((299403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c97 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-460811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1714397/2500000) (δ := 317/25000000) (ψ := -267951/500000) 252 184
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t97 : ((-116977112523/1250000000000 : ℚ) : ℝ) ≤ stT252 97 := by
  have hc : ((-115209/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116977112523/1250000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-115209/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c98 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((987481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -395993/10000000) (δ := 317/25000000) (ψ := -267951/500000) 252 184
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t98 : ((124681924939/1250000000000 : ℚ) : ℝ) ≤ stT252 98 := by
  have hc : ((987431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124681924939/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((987431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c99 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-737399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6000019/10000000) (δ := 317/25000000) (ψ := -267951/500000) 252 184
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t99 : ((-370582134031/5000000000000 : ℚ) : ℝ) ≤ stT252 99 := by
  have hc : ((-737449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-370582134031/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-737449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c100 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((218517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -675251/2000000) (δ := 1263/100000000) (ψ := -267951/500000) 252 185
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t100 : ((218466781533/10000000000000 : ℚ) : ℝ) ≤ stT252 100 := by
  have hc : ((218467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218466781533/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((218467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c101 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((402089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2892497/10000000) (δ := 1263/100000000) (ψ := -267951/500000) 252 185
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t101 : ((400043680443/10000000000000 : ℚ) : ℝ) ≤ stT252 101 := by
  have hc : ((402039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((400043680443/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((402039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c102 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-878451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6608517/10000000) (δ := 12737/1000000000) (ψ := -267951/500000) 252 186
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t102 : ((-217461502037/2500000000000 : ℚ) : ℝ) ≤ stT252 102 := by
  have hc : ((-878501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217461502037/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-878501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c103 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((12287/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -231087/5000000) (δ := 12737/1000000000) (ψ := -267951/500000) 252 186
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t103 : ((96848972739/1000000000000 : ℚ) : ℝ) ≤ stT252 103 := by
  have hc : ((98291/100000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96848972739/1000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((98291/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c104 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-628119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5624823/10000000) (δ := 12737/1000000000) (ψ := -267951/500000) 252 186
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t104 : ((-615970586189/10000000000000 : ℚ) : ℝ) ≤ stT252 104 := by
  have hc : ((-628169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-615970586189/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-628169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c105 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-12731/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1013589/2500000) (δ := 12759/1000000000) (ψ := -267951/500000) 252 187
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t105 : ((-24872788787/5000000000000 : ℚ) : ℝ) ≤ stT252 105 := by
  have hc : ((-25487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24872788787/5000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-25487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c106 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((90009/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 76689/400000) (δ := 12759/1000000000) (ψ := -267951/500000) 252 187
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t106 : ((69934656827/1000000000000 : ℚ) : ℝ) ≤ stT252 106 := by
  have hc : ((360011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69934656827/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((360011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c107 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-249991/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7832799/10000000) (δ := 12759/1000000000) (ψ := -267951/500000) 252 187
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t107 : ((-483375267159/5000000000000 : ℚ) : ℝ) ≤ stT252 107 := by
  have hc : ((-500007/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-483375267159/5000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-500007/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c108 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((69249/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -503663/2500000) (δ := 3163/250000000) (ψ := -267951/500000) 252 188
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t108 : ((66630039/1000000000 : ℚ) : ℝ) ≤ stT252 108 := by
  have hc : ((17311/25000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66630039/1000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((17311/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c109 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((1689/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1895903/5000000) (δ := 3163/250000000) (ψ := -267951/500000) 252 188
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t109 : ((12930172087/2500000000000 : ℚ) : ℝ) ≤ stT252 109 := by
  have hc : ((26999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12930172087/2500000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((26999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c110 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-194939/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3081341/5000000) (δ := 6329/500000000) (ψ := -267951/500000) 252 189
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t110 : ((-371758084089/5000000000000 : ℚ) : ℝ) ≤ stT252 110 := by
  have hc : ((-389903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-371758084089/5000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-389903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c111 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((245757/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -92249/2000000) (δ := 6329/500000000) (ψ := -267951/500000) 252 189
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t111 : ((466500224773/5000000000000 : ℚ) : ℝ) ≤ stT252 111 := by
  have hc : ((491489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((466500224773/5000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((491489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c112 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-241813/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5188973/10000000) (δ := 6329/500000000) (ψ := -267951/500000) 252 189
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t112 : ((-7141113383/156250000000 : ℚ) : ℝ) ≤ stT252 112 := by
  have hc : ((-120919/250000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7141113383/156250000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-120919/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c113 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-386443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -122973/250000) (δ := 6383/500000000) (ψ := -267951/500000) 252 190
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t113 : ((-363582081453/10000000000000 : ℚ) : ℝ) ≤ stT252 113 := by
  have hc : ((-386493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-363582081453/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-386493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c114 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((12103/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 315879/5000000) (δ := 6383/500000000) (ψ := -267951/500000) 252 190
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t114 : ((18135844623/200000000000 : ℚ) : ℝ) ≤ stT252 114 := by
  have hc : ((96819/100000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18135844623/200000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((96819/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c115 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-772519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6133989/10000000) (δ := 6383/500000000) (ψ := -267951/500000) 252 190
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t115 : ((-144084891069/2000000000000 : ℚ) : ℝ) ≤ stT252 115 := by
  have hc : ((-772569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144084891069/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-772569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c116 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-38451/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -823887/2000000) (δ := 1273/100000000) (ψ := -267951/500000) 252 191
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t116 : ((-8931020263/1250000000000 : ℚ) : ℝ) ≤ stT252 116 := by
  have hc : ((-9619/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8931020263/1250000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-9619/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c117 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((870123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1288359/10000000) (δ := 1273/100000000) (ψ := -267951/500000) 252 191
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t117 : ((1608764977/20000000000 : ℚ) : ℝ) ≤ stT252 117 := by
  have hc : ((870073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1608764977/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((870073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c118 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-886277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66501/100000) (δ := 1273/100000000) (ψ := -267951/500000) 252 191
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t118 : ((-32637219121/400000000000 : ℚ) : ℝ) ≤ stT252 118 := by
  have hc : ((-886327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32637219121/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-886327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c119 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((74161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3741419/10000000) (δ := 12623/1000000000) (ψ := -267951/500000) 252 192
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t119 : ((33968702739/5000000000000 : ℚ) : ℝ) ≤ stT252 119 := by
  have hc : ((74111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33968702739/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((74111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c120 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((20459/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 153061/1000000) (δ := 12623/1000000000) (ψ := -267951/500000) 252 192
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t120 : ((7470106497/100000000000 : ℚ) : ℝ) ≤ stT252 120 := by
  have hc : ((81831/100000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7470106497/100000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((81831/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c121 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-45279/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3379427/5000000) (δ := 12623/1000000000) (ψ := -267951/500000) 252 192
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t121 : ((-82330008233/1000000000000 : ℚ) : ℝ) ≤ stT252 121 := by
  have hc : ((-90563/100000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82330008233/1000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-90563/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c122 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((8149/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1881947/5000000) (δ := 12687/1000000000) (ψ := -267951/500000) 252 193
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t122 : ((29488382847/5000000000000 : ℚ) : ℝ) ≤ stT252 122 := by
  have hc : ((32571/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29488382847/5000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((32571/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c123 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((85169/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 275797/2000000) (δ := 12687/1000000000) (ψ := -267951/500000) 252 193
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t123 : ((19197434679/250000000000 : ℚ) : ℝ) ≤ stT252 123 := by
  have hc : ((21291/25000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19197434679/250000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((21291/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c124 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-53299/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6480221/10000000) (δ := 12687/1000000000) (ψ := -267951/500000) 252 193
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t124 : ((-382933979259/5000000000000 : ℚ) : ℝ) ≤ stT252 124 := by
  have hc : ((-426417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-382933979259/5000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-426417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c125 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-48019/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -130233/312500) (δ := 6397/500000000) (ψ := -267951/500000) 252 194
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t125 : ((-2685743677/312500000000 : ℚ) : ℝ) ≤ stT252 125 := by
  have hc : ((-12011/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2685743677/312500000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-12011/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c126 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((942419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 85251/1000000) (δ := 6397/500000000) (ψ := -267951/500000) 252 194
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t126 : ((83952827103/1000000000000 : ℚ) : ℝ) ≤ stT252 126 := by
  have hc : ((942369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83952827103/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((942369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c127 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-345291/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5832723/10000000) (δ := 6397/500000000) (ψ := -267951/500000) 252 194
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t127 : ((-76604642453/1250000000000 : ℚ) : ℝ) ≤ stT252 127 := by
  have hc : ((-86329/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76604642453/1250000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-86329/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c128 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-49001/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -197361/400000) (δ := 12701/1000000000) (ψ := -267951/500000) 252 195
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t128 : ((-43316724159/1250000000000 : ℚ) : ℝ) ≤ stT252 128 := by
  have hc : ((-196029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43316724159/1250000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-196029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c129 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((499961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -31239/10000000) (δ := 12701/1000000000) (ψ := -267951/500000) 252 195
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t129 : ((275105407/3125000000 : ℚ) : ℝ) ≤ stT252 129 := by
  have hc : ((15623/15625 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((275105407/3125000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((15623/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c130 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-70951/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4833621/10000000) (δ := 12701/1000000000) (ψ := -267951/500000) 252 195
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t130 : ((-62236983699/2000000000000 : ℚ) : ℝ) ≤ stT252 130 := by
  have hc : ((-70961/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62236983699/2000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-70961/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c131 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-374943/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1209343/2000000) (δ := 12609/1000000000) (ψ := -267951/500000) 252 196
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t131 : ((-8190285411/125000000000 : ℚ) : ℝ) ≤ stT252 131 := by
  have hc : ((-46871/62500 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8190285411/125000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-46871/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c132 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((175293/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1255817/10000000) (δ := 12609/1000000000) (ψ := -267951/500000) 252 196
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t132 : ((38141054951/500000000000 : ℚ) : ℝ) ≤ stT252 132 := by
  have hc : ((175283/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38141054951/500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((175283/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c133 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((170393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3498919/10000000) (δ := 12609/1000000000) (ψ := -267951/500000) 252 196
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t133 : ((147705948387/10000000000000 : ℚ) : ℝ) ≤ stT252 133 := by
  have hc : ((170343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147705948387/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((170343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c134 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-123677/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1497987/2000000) (δ := 25287/1000000000) (ψ := -267951/500000) 252 197
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t134 : ((-427384501977/5000000000000 : ℚ) : ℝ) ≤ stT252 134 := by
  have hc : ((-494733/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-427384501977/5000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-494733/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c135 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((433551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -701479/2500000) (δ := 3179/250000000) (ψ := -267951/500000) 252 197
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t135 : ((186548918831/5000000000000 : ℚ) : ℝ) ≤ stT252 135 := by
  have hc : ((433501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((186548918831/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((433501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c136 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((740207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1843547/10000000) (δ := 3179/250000000) (ψ := -267951/500000) 252 197
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t136 : ((158669676561/2500000000000 : ℚ) : ℝ) ≤ stT252 136 := by
  have hc : ((740157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158669676561/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((740157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c137 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-424159/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 645899/1000000) (δ := 3179/250000000) (ψ := -267951/500000) 252 197
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t137 : ((-22650312117/312500000000 : ℚ) : ℝ) ≤ stT252 137 := by
  have hc : ((-53023/62500 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22650312117/312500000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-53023/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c138 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-145883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4667173/10000000) (δ := 639/50000000) (ψ := -267951/500000) 252 198
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t138 : ((-31051301589/1250000000000 : ℚ) : ℝ) ≤ stT252 138 := by
  have hc : ((-36477/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31051301589/1250000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-36477/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c139 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((998879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7399/625000) (δ := 639/50000000) (ψ := -267951/500000) 252 198
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t139 : ((211798692963/2500000000000 : ℚ) : ℝ) ≤ stT252 139 := by
  have hc : ((998829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211798692963/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((998829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c140 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-187201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4397771/10000000) (δ := 639/50000000) (ψ := -267951/500000) 252 198
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t140 : ((-31651223781/2000000000000 : ℚ) : ℝ) ≤ stT252 140 := by
  have hc : ((-187251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31651223781/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-187251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c141 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-458341/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -682623/1000000) (δ := 12673/1000000000) (ψ := -267951/500000) 252 199
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t141 : ((-24125865227/312500000000 : ℚ) : ℝ) ≤ stT252 141 := by
  have hc : ((-229183/250000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24125865227/312500000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-229183/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c142 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((582043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1186947/5000000) (δ := 12673/1000000000) (ψ := -267951/500000) 252 199
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t142 : ((488397467733/10000000000000 : ℚ) : ℝ) ≤ stT252 142 := by
  have hc : ((581993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((488397467733/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((581993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c143 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((683041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1023597/5000000) (δ := 12673/1000000000) (ψ := -267951/500000) 252 199
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t143 : ((285572879911/5000000000000 : ℚ) : ℝ) ≤ stT252 143 := by
  have hc : ((682991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((285572879911/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((682991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c144 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-210929/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1609353/2500000) (δ := 12673/1000000000) (ψ := -267951/500000) 252 199
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t144 : ((-175784723961/2500000000000 : ℚ) : ℝ) ≤ stT252 144 := by
  have hc : ((-421883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175784723961/2500000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-421883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c145 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-76677/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1227659/2500000) (δ := 12637/1000000000) (ψ := -267951/500000) 252 200
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t145 : ((-12737020517/400000000000 : ℚ) : ℝ) ≤ stT252 145 := by
  have hc : ((-76687/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12737020517/400000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-76687/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c146 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((973143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -580709/10000000) (δ := 12637/1000000000) (ψ := -267951/500000) 252 200
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t146 : ((161067326453/2000000000000 : ℚ) : ℝ) ≤ stT252 146 := by
  have hc : ((973093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161067326453/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((973093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c147 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((41429/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 464951/1250000) (δ := 12637/1000000000) (ψ := -267951/500000) 252 200
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t147 : ((4268679943/625000000000 : ℚ) : ℝ) ≤ stT252 147 := by
  have hc : ((10351/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4268679943/625000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((10351/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c148 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-499251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -964643/1250000) (δ := 2549/200000000) (ψ := -267951/500000) 252 201
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t148 : ((-20520118781/250000000000 : ℚ) : ℝ) ≤ stT252 148 := by
  have hc : ((-124819/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20520118781/250000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-124819/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c149 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((89973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3474661/10000000) (δ := 2549/200000000) (ψ := -267951/500000) 252 201
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t149 : ((18422047497/1250000000000 : ℚ) : ℝ) ≤ stT252 149 := by
  have hc : ((22487/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18422047497/1250000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((22487/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c150 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((956587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 369673/5000000) (δ := 2549/200000000) (ψ := -267951/500000) 252 201
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t150 : ((48813039647/625000000000 : ℚ) : ℝ) ≤ stT252 150 := by
  have hc : ((956537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48813039647/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((956537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c151 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-24303/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1231361/2500000) (δ := 2549/200000000) (ψ := -267951/500000) 252 201
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t151 : ((-158240457261/5000000000000 : ℚ) : ℝ) ≤ stT252 151 := by
  have hc : ((-194449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158240457261/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-194449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c152 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-13772/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6624079/10000000) (δ := 12751/1000000000) (ψ := -267951/500000) 252 202
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t152 : ((-89369704433/1250000000000 : ℚ) : ℝ) ≤ stT252 152 := by
  have hc : ((-440729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89369704433/1250000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-440729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c153 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((135671/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2492917/10000000) (δ := 12751/1000000000) (ψ := -267951/500000) 252 202
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t153 : ((54836692821/1250000000000 : ℚ) : ℝ) ≤ stT252 153 := by
  have hc : ((271317/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54836692821/1250000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((271317/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c154 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((399689/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 100709/625000) (δ := 12751/1000000000) (ψ := -267951/500000) 252 202
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t154 : ((10064313869/156250000000 : ℚ) : ℝ) ≤ stT252 154 := by
  have hc : ((24979/31250 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10064313869/156250000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((24979/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c155 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-64789/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5689019/10000000) (δ := 12751/1000000000) (ψ := -267951/500000) 252 202
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t155 : ((-1301095917/25000000000 : ℚ) : ℝ) ≤ stT252 155 := by
  have hc : ((-32397/50000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1301095917/25000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-32397/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c156 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-22767/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5967477/10000000) (δ := 3161/250000000) (ψ := -267951/500000) 252 203
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t156 : ((-291671114377/5000000000000 : ℚ) : ℝ) ≤ stT252 156 := by
  have hc : ((-364297/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291671114377/5000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-364297/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c157 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((178297/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1941903/10000000) (δ := 3161/250000000) (ψ := -267951/500000) 252 203
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t157 : ((142286363467/2500000000000 : ℚ) : ℝ) ≤ stT252 157 := by
  have hc : ((356569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142286363467/2500000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((356569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c158 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((679851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2058093/10000000) (δ := 3161/250000000) (ψ := -267951/500000) 252 203
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t158 : ((540820444157/10000000000000 : ℚ) : ℝ) ≤ stT252 158 := by
  have hc : ((679801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((540820444157/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((679801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c159 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-93277/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6032889/10000000) (δ := 3161/250000000) (ψ := -267951/500000) 252 203
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t159 : ((-73978467979/1250000000000 : ℚ) : ℝ) ≤ stT252 159 := by
  have hc : ((-373133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73978467979/1250000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-373133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c160 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-329427/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2862613/5000000) (δ := 6333/500000000) (ψ := -267951/500000) 252 204
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t160 : ((-6511371691/125000000000 : ℚ) : ℝ) ≤ stT252 160 := by
  have hc : ((-82363/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6511371691/125000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-82363/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c161 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((751803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1800011/10000000) (δ := 6333/500000000) (ψ := -267951/500000) 252 204
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t161 : ((59246405683/1000000000000 : ℚ) : ℝ) ≤ stT252 161 := by
  have hc : ((751753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59246405683/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((751753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c162 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((33359/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2100949/10000000) (δ := 6333/500000000) (ψ := -267951/500000) 252 204
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t162 : ((26207334781/500000000000 : ℚ) : ℝ) ≤ stT252 162 := by
  have hc : ((66713/100000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26207334781/500000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((66713/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c163 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-182849/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2988953/5000000) (δ := 6333/500000000) (ψ := -267951/500000) 252 204
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t163 : ((-286456562703/5000000000000 : ℚ) : ℝ) ≤ stT252 163 := by
  have hc : ((-365723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286456562703/5000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-365723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c164 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-17581/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5876851/10000000) (δ := 12773/1000000000) (ψ := -267951/500000) 252 205
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t164 : ((-54917735901/1000000000000 : ℚ) : ℝ) ≤ stT252 164 := by
  have hc : ((-70329/100000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54917735901/1000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-70329/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c165 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((341537/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2047081/10000000) (δ := 12773/1000000000) (ψ := -267951/500000) 252 205
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t165 : ((16616650561/312500000000 : ℚ) : ℝ) ≤ stT252 165 := by
  have hc : ((42689/62500 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16616650561/312500000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((42689/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c166 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((762371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109973/625000) (δ := 12773/1000000000) (ψ := -267951/500000) 252 205
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t166 : ((11833508883/200000000000 : ℚ) : ℝ) ≤ stT252 166 := by
  have hc : ((762321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11833508883/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((762321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c167 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-602451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5543411/10000000) (δ := 12773/1000000000) (ψ := -267951/500000) 252 205
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t167 : ((-7284839591/156250000000 : ℚ) : ℝ) ≤ stT252 167 := by
  have hc : ((-602501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7284839591/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-602501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c168 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-836333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -640339/1000000) (δ := 12723/1000000000) (ψ := -267951/500000) 252 206
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t168 : ((-645283703011/10000000000000 : ℚ) : ℝ) ≤ stT252 168 := by
  have hc : ((-836383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-645283703011/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-836383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c169 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((60477/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1332233/5000000) (δ := 12723/1000000000) (ψ := -267951/500000) 252 206
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t169 : ((18606366009/500000000000 : ℚ) : ℝ) ≤ stT252 169 := by
  have hc : ((241883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18606366009/500000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((241883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c170 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((456353/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 210469/2000000) (δ := 12723/1000000000) (ψ := -267951/500000) 252 206
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t170 : ((10937098381/156250000000 : ℚ) : ℝ) ≤ stT252 170 := by
  have hc : ((57041/62500 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10937098381/156250000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((57041/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c171 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-322289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2373679/5000000) (δ := 12723/1000000000) (ψ := -267951/500000) 252 206
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t171 : ((-3081238501/125000000000 : ℚ) : ℝ) ≤ stT252 171 := by
  have hc : ((-322339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3081238501/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-322339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c172 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-194881/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3643569/5000000) (δ := 2523/200000000) (ψ := -267951/500000) 252 207
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t172 : ((-148603023263/2000000000000 : ℚ) : ℝ) ≤ stT252 172 := by
  have hc : ((-194891/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148603023263/2000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-194891/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c173 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((23309/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -726993/2000000) (δ := 2523/200000000) (ψ := -267951/500000) 252 207
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t173 : ((3542776043/400000000000 : ℚ) : ℝ) ≤ stT252 173 := by
  have hc : ((23299/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3542776043/400000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((23299/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c174 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((999999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1917/5000000) (δ := 2523/200000000) (ψ := -267951/500000) 252 207
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t174 : ((379029668501/5000000000000 : ℚ) : ℝ) ≤ stT252 174 := by
  have hc : ((999949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((379029668501/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((999949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c175 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((127843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3606507/10000000) (δ := 2523/200000000) (ψ := -267951/500000) 252 207
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t175 : ((12075288363/1250000000000 : ℚ) : ℝ) ≤ stT252 175 := by
  have hc : ((127793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12075288363/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((127793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c176 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-96559/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7196247/10000000) (δ := 2523/200000000) (ψ := -267951/500000) 252 207
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t176 : ((-18196978839/250000000000 : ℚ) : ℝ) ≤ stT252 176 := by
  have hc : ((-24141/25000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18196978839/250000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-24141/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c177 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-395037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2471131/5000000) (δ := 2539/200000000) (ψ := -267951/500000) 252 208
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t177 : ((-296965958289/10000000000000 : ℚ) : ℝ) ≤ stT252 177 := by
  have hc : ((-395087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-296965958289/10000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-395087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c178 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((424373/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -174121/1250000) (δ := 2539/200000000) (ψ := -267951/500000) 252 208
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t178 : ((79515495197/1250000000000 : ℚ) : ℝ) ≤ stT252 178 := by
  have hc : ((106087/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79515495197/1250000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((106087/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c179 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((328263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2136481/10000000) (δ := 2539/200000000) (ψ := -267951/500000) 252 208
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t179 : ((24533656953/500000000000 : ℚ) : ℝ) ≤ stT252 179 := by
  have hc : ((164119/250000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24533656953/500000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((164119/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c180 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-9918/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5646211/10000000) (δ := 2539/200000000) (ψ := -267951/500000) 252 208
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t180 : ((-59144184939/1250000000000 : ℚ) : ℝ) ≤ stT252 180 := by
  have hc : ((-317401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59144184939/1250000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-317401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c181 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-174253/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6571427/10000000) (δ := 12801/1000000000) (ψ := -267951/500000) 252 209
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t181 : ((-25905763317/400000000000 : ℚ) : ℝ) ≤ stT252 181 := by
  have hc : ((-174263/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25905763317/400000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-174263/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c182 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((324653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3100379/10000000) (δ := 12801/1000000000) (ψ := -267951/500000) 252 209
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t182 : ((240611649147/10000000000000 : ℚ) : ℝ) ≤ stT252 182 := by
  have hc : ((324603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((240611649147/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((324603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c183 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((990121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 175853/5000000) (δ := 12801/1000000000) (ψ := -267951/500000) 252 209
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t183 : ((731881274691/10000000000000 : ℚ) : ℝ) ≤ stT252 183 := by
  have hc : ((990071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((731881274691/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((990071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c184 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((3549/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1892477/5000000) (δ := 12801/1000000000) (ψ := -267951/500000) 252 209
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t184 : ((20912407703/5000000000000 : ℚ) : ℝ) ≤ stT252 184 := by
  have hc : ((28367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20912407703/5000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((28367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c185 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-48297/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7199617/10000000) (δ := 12801/1000000000) (ψ := -267951/500000) 252 209
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t185 : ((-14204206757/200000000000 : ℚ) : ℝ) ≤ stT252 185 := by
  have hc : ((-96599/100000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14204206757/200000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-96599/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c186 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-456503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2556071/5000000) (δ := 6347/500000000) (ψ := -267951/500000) 252 210
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t186 : ((-83690273877/2500000000000 : ℚ) : ℝ) ≤ stT252 186 := by
  have hc : ((-456553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83690273877/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-456553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c187 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((768929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -867041/5000000) (δ := 6347/500000000) (ψ := -267951/500000) 252 210
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t187 : ((70282460511/1250000000000 : ℚ) : ℝ) ≤ stT252 187 := by
  have hc : ((768879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70282460511/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((768879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c188 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((795867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1625897/10000000) (δ := 6347/500000000) (ψ := -267951/500000) 252 210
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t188 : ((145102109427/2500000000000 : ℚ) : ℝ) ≤ stT252 188 := by
  have hc : ((795817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145102109427/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((795817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c189 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-202257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 496811/1000000) (δ := 6347/500000000) (ψ := -267951/500000) 252 210
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t189 : ((-73569255413/2500000000000 : ℚ) : ℝ) ≤ stT252 189 := by
  have hc : ((-101141/250000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73569255413/2500000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-101141/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c190 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-984647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7415343/10000000) (δ := 1577/125000000) (ψ := -267951/500000) 252 211
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t190 : ((-714375025469/10000000000000 : ℚ) : ℝ) ≤ stT252 190 := by
  have hc : ((-984697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-714375025469/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-984697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c191 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-72429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4108221/10000000) (δ := 1577/125000000) (ψ := -267951/500000) 252 211
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t191 : ((-2097759697/400000000000 : ℚ) : ℝ) ≤ stT252 191 := by
  have hc : ((-72479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2097759697/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-72479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c192 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((946891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -102303/1250000) (δ := 1577/125000000) (ψ := -267951/500000) 252 211
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t192 : ((683322840767/10000000000000 : ℚ) : ℝ) ≤ stT252 192 := by
  have hc : ((946841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((683322840767/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((946841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c193 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((555593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24543/100000) (δ := 1577/125000000) (ψ := -267951/500000) 252 211
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t193 : ((79977636909/2000000000000 : ℚ) : ℝ) ≤ stT252 193 := by
  have hc : ((555543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79977636909/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((555543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c194 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-327151/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 285507/500000) (δ := 1577/125000000) (ψ := -267951/500000) 252 211
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t194 : ((-29362369223/625000000000 : ℚ) : ℝ) ≤ stT252 194 := by
  have hc : ((-40897/62500 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29362369223/625000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-40897/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c195 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-905561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6758741/10000000) (δ := 3181/250000000) (ψ := -267951/500000) 252 212
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t195 : ((-129704324253/2000000000000 : ℚ) : ℝ) ≤ stT252 195 := by
  have hc : ((-905611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129704324253/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-905611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c196 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((155669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -884057/2500000) (δ := 3181/250000000) (ψ := -267951/500000) 252 212
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t196 : ((22231263483/2000000000000 : ℚ) : ℝ) ≤ stT252 196 := by
  have hc : ((155619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22231263483/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((155619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c197 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((15489/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -66019/2000000) (δ := 3181/250000000) (ψ := -267951/500000) 252 212
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t197 : ((35311651881/500000000000 : ℚ) : ℝ) ≤ stT252 197 := by
  have hc : ((495623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35311651881/500000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((495623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c198 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((82807/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 357473/1250000) (δ := 3181/250000000) (ψ := -267951/500000) 252 212
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t198 : ((58841261193/2000000000000 : ℚ) : ℝ) ≤ stT252 198 := by
  have hc : ((82797/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58841261193/2000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((82797/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c199 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-149281/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3016799/5000000) (δ := 3181/250000000) (ψ := -267951/500000) 252 212
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t199 : ((-52914851331/1000000000000 : ℚ) : ℝ) ≤ stT252 199 := by
  have hc : ((-149291/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52914851331/1000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-149291/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c200 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-860271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6516491/10000000) (δ := 3193/250000000) (ψ := -267951/500000) 252 213
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t200 : ((-608339001347/10000000000000 : ℚ) : ℝ) ≤ stT252 200 := by
  have hc : ((-860321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-608339001347/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-860321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c201 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((219279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3374303/10000000) (δ := 3193/250000000) (ψ := -267951/500000) 252 213
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t201 : ((30926415801/2000000000000 : ℚ) : ℝ) ≤ stT252 201 := by
  have hc : ((219229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30926415801/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((219229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c202 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((248773/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -123901/5000000) (δ := 3193/250000000) (ψ := -267951/500000) 252 213
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t202 : ((350054283037/5000000000000 : ℚ) : ℝ) ≤ stT252 202 := by
  have hc : ((497521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((350054283037/5000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((497521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c203 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((82549/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2863327/10000000) (δ := 3193/250000000) (ψ := -267951/500000) 252 213
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t203 : ((28965493809/1000000000000 : ℚ) : ℝ) ≤ stT252 203 := by
  have hc : ((82539/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28965493809/1000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((82539/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c204 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-363129/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5959147/10000000) (δ := 3193/250000000) (ψ := -267951/500000) 252 213
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t204 : ((-127129502357/2500000000000 : ℚ) : ℝ) ≤ stT252 204 := by
  have hc : ((-181577/250000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127129502357/2500000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-181577/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c205 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-111199/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1667029/2500000) (δ := 2533/200000000) (ψ := -267951/500000) 252 214
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t205 : ((-310676775851/5000000000000 : ℚ) : ℝ) ≤ stT252 205 := by
  have hc : ((-444821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-310676775851/5000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-444821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c206 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((32367/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -360241/1000000) (δ := 2533/200000000) (ψ := -267951/500000) 252 214
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t206 : ((45084895697/5000000000000 : ℚ) : ℝ) ≤ stT252 206 := by
  have hc : ((64709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45084895697/5000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((64709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c207 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((12197/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137893/2500000) (δ := 2533/200000000) (ψ := -267951/500000) 252 214
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t207 : ((8477066051/125000000000 : ℚ) : ℝ) ≤ stT252 207 := by
  have hc : ((97571/100000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8477066051/125000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((97571/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c208 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((13637/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2484587/10000000) (δ := 2533/200000000) (ψ := -267951/500000) 252 214
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t208 : ((302550021/8000000000 : ℚ) : ℝ) ≤ stT252 208 := by
  have hc : ((54543/100000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((302550021/8000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((54543/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c209 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-295251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5506193/10000000) (δ := 2533/200000000) (ψ := -267951/500000) 252 214
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t209 : ((-10212341917/250000000000 : ℚ) : ℝ) ≤ stT252 209 := by
  have hc : ((-73819/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10212341917/250000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-73819/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c210 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-482709/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7194591/10000000) (δ := 2529/200000000) (ψ := -267951/500000) 252 215
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t210 : ((-83279580111/1250000000000 : ℚ) : ℝ) ≤ stT252 210 := by
  have hc : ((-241367/250000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83279580111/1250000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-241367/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c211 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-27417/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4201713/10000000) (δ := 2529/200000000) (ψ := -267951/500000) 252 215
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t211 : ((-37766526511/5000000000000 : ℚ) : ℝ) ≤ stT252 211 := by
  have hc : ((-54859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37766526511/5000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-54859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c212 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((882707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -122301/1000000) (δ := 2529/200000000) (ψ := -267951/500000) 252 215
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t212 : ((303105296457/5000000000000 : ℚ) : ℝ) ≤ stT252 212 := by
  have hc : ((882657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((303105296457/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((882657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c213 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((30679/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1741707/10000000) (δ := 2529/200000000) (ψ := -267951/500000) 252 215
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t213 : ((5254878069/100000000000 : ℚ) : ℝ) ≤ stT252 213 := by
  have hc : ((30677/40000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5254878069/100000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((30677/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c214 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-60293/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1173141/2500000) (δ := 2529/200000000) (ψ := -267951/500000) 252 215
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t214 : ((-20611143279/1000000000000 : ℚ) : ℝ) ≤ stT252 214 := by
  have hc : ((-60303/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20611143279/1000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-60303/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c215 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-124497/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 953703/1250000) (δ := 2529/200000000) (ψ := -267951/500000) 252 215
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t215 : ((-67928475187/1000000000000 : ℚ) : ℝ) ≤ stT252 215 := by
  have hc : ((-498013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67928475187/1000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-498013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c216 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-14739/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5154887/10000000) (δ := 797/62500000) (ψ := -267951/500000) 252 216
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t216 : ((-80237480743/2500000000000 : ℚ) : ℝ) ≤ stT252 216 := by
  have hc : ((-235849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80237480743/2500000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-235849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c217 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((311591/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112249/500000) (δ := 797/62500000) (ψ := -267951/500000) 252 216
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t217 : ((26438088713/625000000000 : ℚ) : ℝ) ≤ stT252 217 := by
  have hc : ((155783/250000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26438088713/625000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((155783/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c218 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((241557/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 651571/10000000) (δ := 797/62500000) (ψ := -267951/500000) 252 216
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t218 : ((65437786673/1000000000000 : ℚ) : ℝ) ≤ stT252 218 := by
  have hc : ((483089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65437786673/1000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((483089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c219 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((156197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 883723/2500000) (δ := 797/62500000) (ψ := -267951/500000) 252 216
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t219 : ((105514305339/10000000000000 : ℚ) : ℝ) ≤ stT252 219 := by
  have hc : ((156147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105514305339/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((156147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c220 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-104587/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3202523/5000000) (δ := 797/62500000) (ψ := -267951/500000) 252 216
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t220 : ((-1410335383/25000000000 : ℚ) : ℝ) ≤ stT252 220 := by
  have hc : ((-418373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1410335383/25000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-418373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c221 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-1691/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3222871/5000000) (δ := 1593/125000000) (ψ := -267951/500000) 252 217
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t221 : ((-11375573103/200000000000 : ℚ) : ℝ) ≤ stT252 221 := by
  have hc : ((-16911/20000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11375573103/200000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-16911/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c222 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((129811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -450193/1250000) (δ := 1593/125000000) (ψ := -267951/500000) 252 217
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t222 : ((21772468429/2500000000000 : ℚ) : ℝ) ≤ stT252 222 := by
  have hc : ((129761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21772468429/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((129761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c223 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((952933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -96259/1250000) (δ := 1593/125000000) (ψ := -267951/500000) 252 217
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t223 : ((638097148067/10000000000000 : ℚ) : ℝ) ≤ stT252 223 := by
  have hc : ((952883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((638097148067/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((952883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c224 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((68259/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2048737/10000000) (δ := 1593/125000000) (ψ := -267951/500000) 252 217
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t224 : ((22802057431/500000000000 : ℚ) : ℝ) ≤ stT252 224 := by
  have hc : ((34127/50000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22802057431/500000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((34127/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c225 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-362741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4855009/10000000) (δ := 1593/125000000) (ψ := -267951/500000) 252 217
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t225 : ((-241860787597/10000000000000 : ℚ) : ℝ) ≤ stT252 225 := by
  have hc : ((-362791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-241860787597/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-362791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c226 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-996633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 956097/1250000) (δ := 25259/1000000000) (ψ := -267951/500000) 252 217
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t226 : ((-662984561453/10000000000000 : ℚ) : ℝ) ≤ stT252 226 := by
  have hc : ((-996683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-662984561453/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-996683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c227 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-514381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2638853/5000000) (δ := 3159/250000000) (ψ := -267951/500000) 252 218
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t227 : ((-85360050261/2500000000000 : ℚ) : ℝ) ≤ stT252 227 := by
  have hc : ((-514431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85360050261/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-514431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c228 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((268723/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1254239/5000000) (δ := 3159/250000000) (ψ := -267951/500000) 252 218
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t228 : ((44487387417/1250000000000 : ℚ) : ℝ) ≤ stT252 228 := by
  have hc : ((134349/250000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44487387417/1250000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((134349/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c229 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((497529/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 124327/5000000) (δ := 3159/250000000) (ψ := -267951/500000) 252 218
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t229 : ((5136868723/78125000000 : ℚ) : ℝ) ≤ stT252 229 := by
  have hc : ((15547/15625 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5136868723/78125000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((15547/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c230 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((182343/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2993753/10000000) (δ := 3159/250000000) (ψ := -267951/500000) 252 218
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t230 : ((3005421071/125000000000 : ℚ) : ℝ) ≤ stT252 230 := by
  have hc : ((91159/250000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3005421071/125000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((91159/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c231 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-659371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1145389/2000000) (δ := 3159/250000000) (ψ := -267951/500000) 252 218
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t231 : ((-13558355181/312500000000 : ℚ) : ℝ) ≤ stT252 231 := by
  have hc : ((-659421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13558355181/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-659421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c232 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-242969/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -725967/1000000) (δ := 6337/500000000) (ψ := -267951/500000) 252 219
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t232 : ((-319050746279/5000000000000 : ℚ) : ℝ) ≤ stT252 232 := by
  have hc : ((-485963/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-319050746279/5000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-485963/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c233 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-246623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4549977/10000000) (δ := 6337/500000000) (ψ := -267951/500000) 252 219
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t233 : ((-80800454553/5000000000000 : ℚ) : ℝ) ≤ stT252 233 := by
  have hc : ((-246673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80800454553/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-246673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c234 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((368981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -462969/2500000) (δ := 6337/500000000) (ψ := -267951/500000) 252 219
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t234 : ((1507461977/31250000000 : ℚ) : ℝ) ≤ stT252 234 := by
  have hc : ((92239/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1507461977/31250000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((92239/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c235 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((472389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 104337/1250000) (δ := 6337/500000000) (ψ := -267951/500000) 252 219
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t235 : ((9629258231/156250000000 : ℚ) : ℝ) ≤ stT252 235 := by
  have hc : ((118091/125000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9629258231/156250000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((118091/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c236 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((166077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 701973/2000000) (δ := 6337/500000000) (ψ := -267951/500000) 252 219
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t236 : ((1688660617/156250000000 : ℚ) : ℝ) ≤ stT252 236 := by
  have hc : ((166027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1688660617/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((166027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c237 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-391253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3086847/5000000) (δ := 6337/500000000) (ψ := -267951/500000) 252 219
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t237 : ((-12708122523/250000000000 : ℚ) : ℝ) ≤ stT252 237 := by
  have hc : ((-195639/250000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12708122523/250000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-195639/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c238 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-185063/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3440827/5000000) (δ := 12781/1000000000) (ψ := -267951/500000) 252 220
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t238 : ((-29991264723/500000000000 : ℚ) : ℝ) ≤ stT252 238 := by
  have hc : ((-185073/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29991264723/500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-185073/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c239 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-124927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4240127/10000000) (δ := 12781/1000000000) (ψ := -267951/500000) 252 220
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t239 : ((-80840997519/10000000000000 : ℚ) : ℝ) ≤ stT252 239 := by
  have hc : ((-124977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80840997519/10000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-124977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c240 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((799791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12877/80000) (δ := 12781/1000000000) (ψ := -267951/500000) 252 220
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t240 : ((516230416277/10000000000000 : ℚ) : ℝ) ≤ stT252 240 := by
  have hc : ((799741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((516230416277/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((799741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c241 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((919509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 201983/2000000) (δ := 12781/1000000000) (ψ := -267951/500000) 252 220
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t241 : ((148068757901/2500000000000 : ℚ) : ℝ) ≤ stT252 241 := by
  have hc : ((919459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148068757901/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((919459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c242 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((30759/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3618619/10000000) (δ := 12781/1000000000) (ψ := -267951/500000) 252 220
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t242 : ((4941147029/625000000000 : ℚ) : ℝ) ≤ stT252 242 := by
  have hc : ((61493/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4941147029/625000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((61493/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c243 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-158613/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 124331/200000) (δ := 12781/1000000000) (ψ := -267951/500000) 252 220
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t243 : ((-101756813123/2000000000000 : ℚ) : ℝ) ≤ stT252 243 := by
  have hc : ((-158623/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101756813123/2000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-158623/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c244 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-928687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -690413/1000000) (δ := 2543/200000000) (ψ := -267951/500000) 252 221
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t244 : ((-118912699269/2000000000000 : ℚ) : ℝ) ≤ stT252 244 := by
  have hc : ((-928737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118912699269/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-928737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c245 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-9969/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4327461/10000000) (δ := 3161/125000000) (ψ := -267951/500000) 252 221
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t245 : ((-50967690429/5000000000000 : ℚ) : ℝ) ≤ stT252 245 := by
  have hc : ((-79777/500000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50967690429/5000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-79777/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c246 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((152387/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1761251/10000000) (δ := 2543/200000000) (ψ := -267951/500000) 252 221
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t246 : ((12143989769/250000000000 : ℚ) : ℝ) ≤ stT252 246 := by
  have hc : ((152377/200000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12143989769/250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((152377/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c247 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((949921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 794533/10000000) (δ := 2543/200000000) (ψ := -267951/500000) 252 221
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t247 : ((151096929841/2500000000000 : ℚ) : ℝ) ≤ stT252 247 := by
  have hc : ((949871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151096929841/2500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((949871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c248 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((232651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 667997/2000000) (δ := 2543/200000000) (ψ := -267951/500000) 252 221
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t248 : ((29540327/2000000000 : ℚ) : ℝ) ≤ stT252 248 := by
  have hc : ((232601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29540327/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((232601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c249 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-702761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183599/312500) (δ := 2543/200000000) (ψ := -267951/500000) 252 221
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t249 : ((-17815556039/400000000000 : ℚ) : ℝ) ≤ stT252 249 := by
  have hc : ((-702811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17815556039/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-702811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_c250 :
    |Real.cos (((252 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-48811/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1826923/2500000) (δ := 197/15625000) (ψ := -267951/500000) 252 222
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st252_t250 : ((-7718097739/125000000000 : ℚ) : ℝ) ≤ stT252 250 := by
  have hc : ((-97627/100000 : ℚ) : ℝ)
      ≤ Real.cos (((252 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st252_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7718097739/125000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-97627/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st252_p1 : ((429879/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT252 (i+1) := by
  rw [Finset.sum_range_one]
  exact st252_t1

theorem st252_p2 : ((13912342449607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT252 (i+1))
      = (∑ i ∈ Finset.range 1, stT252 (i+1)) + stT252 2 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 1
    simpa using h
  have hprev := st252_p1
  have hstep := st252_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p3 : ((17381968891021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT252 (i+1))
      = (∑ i ∈ Finset.range 2, stT252 (i+1)) + stT252 3 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 2
    simpa using h
  have hprev := st252_p2
  have hstep := st252_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p4 : ((1540931349649/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT252 (i+1))
      = (∑ i ∈ Finset.range 3, stT252 (i+1)) + stT252 4 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 3
    simpa using h
  have hprev := st252_p3
  have hstep := st252_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p5 : ((6226785741413/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT252 (i+1))
      = (∑ i ∈ Finset.range 4, stT252 (i+1)) + stT252 5 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 4
    simpa using h
  have hprev := st252_p4
  have hstep := st252_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p6 : ((4078872306953/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT252 (i+1))
      = (∑ i ∈ Finset.range 5, stT252 (i+1)) + stT252 6 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 5
    simpa using h
  have hprev := st252_p5
  have hstep := st252_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p7 : ((2362833360593/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT252 (i+1))
      = (∑ i ∈ Finset.range 6, stT252 (i+1)) + stT252 7 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 6
    simpa using h
  have hprev := st252_p6
  have hstep := st252_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p8 : ((3845380627031/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT252 (i+1))
      = (∑ i ∈ Finset.range 7, stT252 (i+1)) + stT252 8 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 7
    simpa using h
  have hprev := st252_p7
  have hstep := st252_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p9 : ((16220932424183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT252 (i+1))
      = (∑ i ∈ Finset.range 8, stT252 (i+1)) + stT252 9 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 8
    simpa using h
  have hprev := st252_p8
  have hstep := st252_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p10 : ((2663439822237/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT252 (i+1))
      = (∑ i ∈ Finset.range 9, stT252 (i+1)) + stT252 10 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 9
    simpa using h
  have hprev := st252_p9
  have hstep := st252_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p11 : ((2633921856177/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT252 (i+1))
      = (∑ i ∈ Finset.range 10, stT252 (i+1)) + stT252 11 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 10
    simpa using h
  have hprev := st252_p10
  have hstep := st252_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p12 : ((13125135979573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT252 (i+1))
      = (∑ i ∈ Finset.range 11, stT252 (i+1)) + stT252 12 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 11
    simpa using h
  have hprev := st252_p11
  have hstep := st252_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p13 : ((15801718795573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT252 (i+1))
      = (∑ i ∈ Finset.range 12, stT252 (i+1)) + stT252 13 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 12
    simpa using h
  have hprev := st252_p12
  have hstep := st252_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p14 : ((18220446018633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT252 (i+1))
      = (∑ i ∈ Finset.range 13, stT252 (i+1)) + stT252 14 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 13
    simpa using h
  have hprev := st252_p13
  have hstep := st252_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p15 : ((8689576980387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT252 (i+1))
      = (∑ i ∈ Finset.range 14, stT252 (i+1)) + stT252 15 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 14
    simpa using h
  have hprev := st252_p14
  have hstep := st252_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p16 : ((32859255349/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT252 (i+1))
      = (∑ i ∈ Finset.range 15, stT252 (i+1)) + stT252 16 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 15
    simpa using h
  have hprev := st252_p15
  have hstep := st252_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p17 : ((16326146341223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT252 (i+1))
      = (∑ i ∈ Finset.range 16, stT252 (i+1)) + stT252 17 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 16
    simpa using h
  have hprev := st252_p16
  have hstep := st252_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p18 : ((18678796065413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT252 (i+1))
      = (∑ i ∈ Finset.range 17, stT252 (i+1)) + stT252 18 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 17
    simpa using h
  have hprev := st252_p17
  have hstep := st252_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p19 : ((3936197874847/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT252 (i+1))
      = (∑ i ∈ Finset.range 18, stT252 (i+1)) + stT252 19 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 18
    simpa using h
  have hprev := st252_p18
  have hstep := st252_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p20 : ((19887651158509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT252 (i+1))
      = (∑ i ∈ Finset.range 19, stT252 (i+1)) + stT252 20 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 19
    simpa using h
  have hprev := st252_p19
  have hstep := st252_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p21 : ((20664113734469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT252 (i+1))
      = (∑ i ∈ Finset.range 20, stT252 (i+1)) + stT252 21 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 20
    simpa using h
  have hprev := st252_p20
  have hstep := st252_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p22 : ((2832076607053/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT252 (i+1))
      = (∑ i ∈ Finset.range 21, stT252 (i+1)) + stT252 22 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 21
    simpa using h
  have hprev := st252_p21
  have hstep := st252_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p23 : ((2972692984267/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT252 (i+1))
      = (∑ i ∈ Finset.range 22, stT252 (i+1)) + stT252 23 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 22
    simpa using h
  have hprev := st252_p22
  have hstep := st252_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p24 : ((341108966309/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT252 (i+1))
      = (∑ i ∈ Finset.range 23, stT252 (i+1)) + stT252 24 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 23
    simpa using h
  have hprev := st252_p23
  have hstep := st252_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p25 : ((353537716309/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT252 (i+1))
      = (∑ i ∈ Finset.range 24, stT252 (i+1)) + stT252 25 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 24
    simpa using h
  have hprev := st252_p24
  have hstep := st252_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p26 : ((22723850205739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT252 (i+1))
      = (∑ i ∈ Finset.range 25, stT252 (i+1)) + stT252 26 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 25
    simpa using h
  have hprev := st252_p25
  have hstep := st252_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p27 : ((350995643423/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT252 (i+1))
      = (∑ i ∈ Finset.range 26, stT252 (i+1)) + stT252 27 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 26
    simpa using h
  have hprev := st252_p26
  have hstep := st252_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p28 : ((444575794453/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT252 (i+1))
      = (∑ i ∈ Finset.range 27, stT252 (i+1)) + stT252 28 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 27
    simpa using h
  have hprev := st252_p27
  have hstep := st252_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p29 : ((23433983787851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT252 (i+1))
      = (∑ i ∈ Finset.range 28, stT252 (i+1)) + stT252 29 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 28
    simpa using h
  have hprev := st252_p28
  have hstep := st252_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p30 : ((864336755393/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT252 (i+1))
      = (∑ i ∈ Finset.range 29, stT252 (i+1)) + stT252 30 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 29
    simpa using h
  have hprev := st252_p29
  have hstep := st252_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p31 : ((2786793012237/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT252 (i+1))
      = (∑ i ∈ Finset.range 30, stT252 (i+1)) + stT252 31 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 30
    simpa using h
  have hprev := st252_p30
  have hstep := st252_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p32 : ((2976469000739/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT252 (i+1))
      = (∑ i ∈ Finset.range 31, stT252 (i+1)) + stT252 32 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 31
    simpa using h
  have hprev := st252_p31
  have hstep := st252_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p33 : ((720989722157/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT252 (i+1))
      = (∑ i ∈ Finset.range 32, stT252 (i+1)) + stT252 33 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 32
    simpa using h
  have hprev := st252_p32
  have hstep := st252_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p34 : ((2136659944309/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT252 (i+1))
      = (∑ i ∈ Finset.range 33, stT252 (i+1)) + stT252 34 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 33
    simpa using h
  have hprev := st252_p33
  have hstep := st252_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p35 : ((20644876377197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT252 (i+1))
      = (∑ i ∈ Finset.range 34, stT252 (i+1)) + stT252 35 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 34
    simpa using h
  have hprev := st252_p34
  have hstep := st252_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p36 : ((21254921133179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT252 (i+1))
      = (∑ i ∈ Finset.range 35, stT252 (i+1)) + stT252 36 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 35
    simpa using h
  have hprev := st252_p35
  have hstep := st252_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p37 : ((22634780284483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT252 (i+1))
      = (∑ i ∈ Finset.range 36, stT252 (i+1)) + stT252 37 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 36
    simpa using h
  have hprev := st252_p36
  have hstep := st252_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p38 : ((24241615695763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT252 (i+1))
      = (∑ i ∈ Finset.range 37, stT252 (i+1)) + stT252 38 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 37
    simpa using h
  have hprev := st252_p37
  have hstep := st252_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p39 : ((12915141702663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT252 (i+1))
      = (∑ i ∈ Finset.range 38, stT252 (i+1)) + stT252 39 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 38
    simpa using h
  have hprev := st252_p38
  have hstep := st252_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p40 : ((6843126213933/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT252 (i+1))
      = (∑ i ∈ Finset.range 39, stT252 (i+1)) + stT252 40 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 39
    simpa using h
  have hprev := st252_p39
  have hstep := st252_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p41 : ((14456927470467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT252 (i+1))
      = (∑ i ∈ Finset.range 40, stT252 (i+1)) + stT252 41 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 40
    simpa using h
  have hprev := st252_p40
  have hstep := st252_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p42 : ((30454948348453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT252 (i+1))
      = (∑ i ∈ Finset.range 41, stT252 (i+1)) + stT252 42 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 41
    simpa using h
  have hprev := st252_p41
  have hstep := st252_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p43 : ((3982237815471/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT252 (i+1))
      = (∑ i ∈ Finset.range 42, stT252 (i+1)) + stT252 43 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 42
    simpa using h
  have hprev := st252_p42
  have hstep := st252_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p44 : ((8200950488213/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT252 (i+1))
      = (∑ i ∈ Finset.range 43, stT252 (i+1)) + stT252 44 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 43
    simpa using h
  have hprev := st252_p43
  have hstep := st252_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p45 : ((32890562823763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT252 (i+1))
      = (∑ i ∈ Finset.range 44, stT252 (i+1)) + stT252 45 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 44
    simpa using h
  have hprev := st252_p44
  have hstep := st252_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p46 : ((31956273000043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT252 (i+1))
      = (∑ i ∈ Finset.range 45, stT252 (i+1)) + stT252 46 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 45
    simpa using h
  have hprev := st252_p45
  have hstep := st252_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p47 : ((30497870970543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT252 (i+1))
      = (∑ i ∈ Finset.range 46, stT252 (i+1)) + stT252 47 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 46
    simpa using h
  have hprev := st252_p46
  have hstep := st252_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p48 : ((29666154418063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT252 (i+1))
      = (∑ i ∈ Finset.range 47, stT252 (i+1)) + stT252 48 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 47
    simpa using h
  have hprev := st252_p47
  have hstep := st252_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p49 : ((606340141599/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT252 (i+1))
      = (∑ i ∈ Finset.range 48, stT252 (i+1)) + stT252 49 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 48
    simpa using h
  have hprev := st252_p48
  have hstep := st252_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p50 : ((31724854707237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT252 (i+1))
      = (∑ i ∈ Finset.range 49, stT252 (i+1)) + stT252 50 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 49
    simpa using h
  have hprev := st252_p49
  have hstep := st252_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p51 : ((31980274180917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT252 (i+1))
      = (∑ i ∈ Finset.range 50, stT252 (i+1)) + stT252 51 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 50
    simpa using h
  have hprev := st252_p50
  have hstep := st252_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p52 : ((30684538422549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT252 (i+1))
      = (∑ i ∈ Finset.range 51, stT252 (i+1)) + stT252 52 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 51
    simpa using h
  have hprev := st252_p51
  have hstep := st252_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p53 : ((30084262985307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT252 (i+1))
      = (∑ i ∈ Finset.range 52, stT252 (i+1)) + stT252 53 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 52
    simpa using h
  have hprev := st252_p52
  have hstep := st252_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p54 : ((3913676091159/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT252 (i+1))
      = (∑ i ∈ Finset.range 53, stT252 (i+1)) + stT252 54 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 53
    simpa using h
  have hprev := st252_p53
  have hstep := st252_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p55 : ((31786640845347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT252 (i+1))
      = (∑ i ∈ Finset.range 54, stT252 (i+1)) + stT252 55 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 54
    simpa using h
  have hprev := st252_p54
  have hstep := st252_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p56 : ((7618584481997/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT252 (i+1))
      = (∑ i ∈ Finset.range 55, stT252 (i+1)) + stT252 56 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 55
    simpa using h
  have hprev := st252_p55
  have hstep := st252_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p57 : ((3819542297447/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT252 (i+1))
      = (∑ i ∈ Finset.range 56, stT252 (i+1)) + stT252 57 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 56
    simpa using h
  have hprev := st252_p56
  have hstep := st252_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p58 : ((124101211747/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT252 (i+1))
      = (∑ i ∈ Finset.range 57, stT252 (i+1)) + stT252 58 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 57
    simpa using h
  have hprev := st252_p57
  have hstep := st252_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p59 : ((1927458103147/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT252 (i+1))
      = (∑ i ∈ Finset.range 58, stT252 (i+1)) + stT252 59 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 58
    simpa using h
  have hprev := st252_p58
  have hstep := st252_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p60 : ((30460782805457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT252 (i+1))
      = (∑ i ∈ Finset.range 59, stT252 (i+1)) + stT252 60 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 59
    simpa using h
  have hprev := st252_p59
  have hstep := st252_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p61 : ((31701452995617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT252 (i+1))
      = (∑ i ∈ Finset.range 60, stT252 (i+1)) + stT252 61 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 60
    simpa using h
  have hprev := st252_p60
  have hstep := st252_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p62 : ((30735451374357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT252 (i+1))
      = (∑ i ∈ Finset.range 61, stT252 (i+1)) + stT252 62 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 61
    simpa using h
  have hprev := st252_p61
  have hstep := st252_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p63 : ((30702254743539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT252 (i+1))
      = (∑ i ∈ Finset.range 62, stT252 (i+1)) + stT252 63 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 62
    simpa using h
  have hprev := st252_p62
  have hstep := st252_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p64 : ((31643994743539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT252 (i+1))
      = (∑ i ∈ Finset.range 63, stT252 (i+1)) + stT252 64 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 63
    simpa using h
  have hprev := st252_p63
  have hstep := st252_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p65 : ((30405009885991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT252 (i+1))
      = (∑ i ∈ Finset.range 64, stT252 (i+1)) + stT252 65 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 64
    simpa using h
  have hprev := st252_p64
  have hstep := st252_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p66 : ((6260485486463/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT252 (i+1))
      = (∑ i ∈ Finset.range 65, stT252 (i+1)) + stT252 66 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 65
    simpa using h
  have hprev := st252_p65
  have hstep := st252_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p67 : ((6219359079/2000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT252 (i+1))
      = (∑ i ∈ Finset.range 66, stT252 (i+1)) + stT252 67 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 66
    simpa using h
  have hprev := st252_p66
  have hstep := st252_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p68 : ((478112791393/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT252 (i+1))
      = (∑ i ∈ Finset.range 67, stT252 (i+1)) + stT252 68 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 67
    simpa using h
  have hprev := st252_p67
  have hstep := st252_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p69 : ((61690196483/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT252 (i+1))
      = (∑ i ∈ Finset.range 68, stT252 (i+1)) + stT252 69 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 68
    simpa using h
  have hprev := st252_p68
  have hstep := st252_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p70 : ((30399626179579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT252 (i+1))
      = (∑ i ∈ Finset.range 69, stT252 (i+1)) + stT252 70 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 69
    simpa using h
  have hprev := st252_p69
  have hstep := st252_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p71 : ((31531024857433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT252 (i+1))
      = (∑ i ∈ Finset.range 70, stT252 (i+1)) + stT252 71 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 70
    simpa using h
  have hprev := st252_p70
  have hstep := st252_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p72 : ((30621661427993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT252 (i+1))
      = (∑ i ∈ Finset.range 71, stT252 (i+1)) + stT252 72 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 71
    simpa using h
  have hprev := st252_p71
  have hstep := st252_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p73 : ((7807587806177/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT252 (i+1))
      = (∑ i ∈ Finset.range 72, stT252 (i+1)) + stT252 73 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 72
    simpa using h
  have hprev := st252_p72
  have hstep := st252_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p74 : ((6186295910097/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT252 (i+1))
      = (∑ i ∈ Finset.range 73, stT252 (i+1)) + stT252 74 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 73
    simpa using h
  have hprev := st252_p73
  have hstep := st252_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p75 : ((6190657904817/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT252 (i+1))
      = (∑ i ∈ Finset.range 74, stT252 (i+1)) + stT252 75 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 74
    simpa using h
  have hprev := st252_p74
  have hstep := st252_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p76 : ((31155498728081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT252 (i+1))
      = (∑ i ∈ Finset.range 75, stT252 (i+1)) + stT252 76 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 75
    simpa using h
  have hprev := st252_p75
  have hstep := st252_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p77 : ((30786337039653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT252 (i+1))
      = (∑ i ∈ Finset.range 76, stT252 (i+1)) + stT252 77 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 76
    simpa using h
  have hprev := st252_p76
  have hstep := st252_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p78 : ((3908557431747/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT252 (i+1))
      = (∑ i ∈ Finset.range 77, stT252 (i+1)) + stT252 78 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 77
    simpa using h
  have hprev := st252_p77
  have hstep := st252_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p79 : ((3840075012819/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT252 (i+1))
      = (∑ i ∈ Finset.range 78, stT252 (i+1)) + stT252 79 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 78
    simpa using h
  have hprev := st252_p78
  have hstep := st252_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p80 : ((31292293978739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT252 (i+1))
      = (∑ i ∈ Finset.range 79, stT252 (i+1)) + stT252 80 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 79
    simpa using h
  have hprev := st252_p79
  have hstep := st252_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p81 : ((30734683532651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT252 (i+1))
      = (∑ i ∈ Finset.range 80, stT252 (i+1)) + stT252 81 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 80
    simpa using h
  have hprev := st252_p80
  have hstep := st252_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p82 : ((3905100405577/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT252 (i+1))
      = (∑ i ∈ Finset.range 81, stT252 (i+1)) + stT252 82 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 81
    simpa using h
  have hprev := st252_p81
  have hstep := st252_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p83 : ((1541215020649/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT252 (i+1))
      = (∑ i ∈ Finset.range 82, stT252 (i+1)) + stT252 83 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 82
    simpa using h
  have hprev := st252_p82
  have hstep := st252_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p84 : ((31110587982423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT252 (i+1))
      = (∑ i ∈ Finset.range 83, stT252 (i+1)) + stT252 84 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 83
    simpa using h
  have hprev := st252_p83
  have hstep := st252_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p85 : ((6199104296853/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT252 (i+1))
      = (∑ i ∈ Finset.range 84, stT252 (i+1)) + stT252 85 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 84
    simpa using h
  have hprev := st252_p84
  have hstep := st252_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p86 : ((30900735374737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT252 (i+1))
      = (∑ i ∈ Finset.range 85, stT252 (i+1)) + stT252 86 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 85
    simpa using h
  have hprev := st252_p85
  have hstep := st252_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p87 : ((31234073221441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT252 (i+1))
      = (∑ i ∈ Finset.range 86, stT252 (i+1)) + stT252 87 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 86
    simpa using h
  have hprev := st252_p86
  have hstep := st252_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p88 : ((30651813308609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT252 (i+1))
      = (∑ i ∈ Finset.range 87, stT252 (i+1)) + stT252 88 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 87
    simpa using h
  have hprev := st252_p87
  have hstep := st252_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p89 : ((31463236772121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT252 (i+1))
      = (∑ i ∈ Finset.range 88, stT252 (i+1)) + stT252 89 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 88
    simpa using h
  have hprev := st252_p88
  have hstep := st252_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p90 : ((952548979371/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT252 (i+1))
      = (∑ i ∈ Finset.range 89, stT252 (i+1)) + stT252 90 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 89
    simpa using h
  have hprev := st252_p89
  have hstep := st252_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p91 : ((7882416448401/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT252 (i+1))
      = (∑ i ∈ Finset.range 90, stT252 (i+1)) + stT252 91 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 90
    simpa using h
  have hprev := st252_p90
  have hstep := st252_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p92 : ((190988544251/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT252 (i+1))
      = (∑ i ∈ Finset.range 91, stT252 (i+1)) + stT252 92 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 91
    simpa using h
  have hprev := st252_p91
  have hstep := st252_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p93 : ((15644439744567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT252 (i+1))
      = (∑ i ∈ Finset.range 92, stT252 (i+1)) + stT252 93 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 92
    simpa using h
  have hprev := st252_p92
  have hstep := st252_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p94 : ((7737272214219/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT252 (i+1))
      = (∑ i ∈ Finset.range 93, stT252 (i+1)) + stT252 94 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 93
    simpa using h
  have hprev := st252_p93
  have hstep := st252_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p95 : ((30806634750663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT252 (i+1))
      = (∑ i ∈ Finset.range 94, stT252 (i+1)) + stT252 95 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 94
    simpa using h
  have hprev := st252_p94
  have hstep := st252_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p96 : ((31417788130383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT252 (i+1))
      = (∑ i ∈ Finset.range 95, stT252 (i+1)) + stT252 96 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 95
    simpa using h
  have hprev := st252_p95
  have hstep := st252_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p97 : ((30481971230199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT252 (i+1))
      = (∑ i ∈ Finset.range 96, stT252 (i+1)) + stT252 97 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 96
    simpa using h
  have hprev := st252_p96
  have hstep := st252_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p98 : ((31479426629711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT252 (i+1))
      = (∑ i ∈ Finset.range 97, stT252 (i+1)) + stT252 98 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 97
    simpa using h
  have hprev := st252_p97
  have hstep := st252_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p99 : ((30738262361649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT252 (i+1))
      = (∑ i ∈ Finset.range 98, stT252 (i+1)) + stT252 99 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 98
    simpa using h
  have hprev := st252_p98
  have hstep := st252_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p100 : ((15478364571591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT252 (i+1))
      = (∑ i ∈ Finset.range 99, stT252 (i+1)) + stT252 100 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 99
    simpa using h
  have hprev := st252_p99
  have hstep := st252_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p101 : ((250854182589/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT252 (i+1))
      = (∑ i ∈ Finset.range 100, stT252 (i+1)) + stT252 101 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 100
    simpa using h
  have hprev := st252_p100
  have hstep := st252_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p102 : ((30486926815477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT252 (i+1))
      = (∑ i ∈ Finset.range 101, stT252 (i+1)) + stT252 102 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 101
    simpa using h
  have hprev := st252_p101
  have hstep := st252_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p103 : ((31455416542867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT252 (i+1))
      = (∑ i ∈ Finset.range 102, stT252 (i+1)) + stT252 103 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 102
    simpa using h
  have hprev := st252_p102
  have hstep := st252_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p104 : ((15419722978339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT252 (i+1))
      = (∑ i ∈ Finset.range 103, stT252 (i+1)) + stT252 104 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 103
    simpa using h
  have hprev := st252_p103
  have hstep := st252_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p105 : ((962178136847/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT252 (i+1))
      = (∑ i ∈ Finset.range 104, stT252 (i+1)) + stT252 105 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 104
    simpa using h
  have hprev := st252_p104
  have hstep := st252_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p106 : ((15744523473687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT252 (i+1))
      = (∑ i ∈ Finset.range 105, stT252 (i+1)) + stT252 106 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 105
    simpa using h
  have hprev := st252_p105
  have hstep := st252_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p107 : ((238455440727/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT252 (i+1))
      = (∑ i ∈ Finset.range 106, stT252 (i+1)) + stT252 107 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 106
    simpa using h
  have hprev := st252_p106
  have hstep := st252_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p108 : ((1949287300191/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT252 (i+1))
      = (∑ i ∈ Finset.range 107, stT252 (i+1)) + stT252 108 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 107
    simpa using h
  have hprev := st252_p107
  have hstep := st252_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p109 : ((7810079372851/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT252 (i+1))
      = (∑ i ∈ Finset.range 108, stT252 (i+1)) + stT252 109 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 108
    simpa using h
  have hprev := st252_p108
  have hstep := st252_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p110 : ((15248400661613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT252 (i+1))
      = (∑ i ∈ Finset.range 109, stT252 (i+1)) + stT252 110 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 109
    simpa using h
  have hprev := st252_p109
  have hstep := st252_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p111 : ((7857450443193/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT252 (i+1))
      = (∑ i ∈ Finset.range 110, stT252 (i+1)) + stT252 111 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 110
    simpa using h
  have hprev := st252_p110
  have hstep := st252_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p112 : ((1548638525813/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT252 (i+1))
      = (∑ i ∈ Finset.range 111, stT252 (i+1)) + stT252 112 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 111
    simpa using h
  have hprev := st252_p111
  have hstep := st252_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p113 : ((30609188434807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT252 (i+1))
      = (∑ i ∈ Finset.range 112, stT252 (i+1)) + stT252 113 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 112
    simpa using h
  have hprev := st252_p112
  have hstep := st252_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p114 : ((31515980665957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT252 (i+1))
      = (∑ i ∈ Finset.range 113, stT252 (i+1)) + stT252 114 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 113
    simpa using h
  have hprev := st252_p113
  have hstep := st252_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p115 : ((7698889052653/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT252 (i+1))
      = (∑ i ∈ Finset.range 114, stT252 (i+1)) + stT252 115 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 114
    simpa using h
  have hprev := st252_p114
  have hstep := st252_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p116 : ((7681027012127/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT252 (i+1))
      = (∑ i ∈ Finset.range 115, stT252 (i+1)) + stT252 116 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 115
    simpa using h
  have hprev := st252_p115
  have hstep := st252_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p117 : ((1970530658563/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT252 (i+1))
      = (∑ i ∈ Finset.range 116, stT252 (i+1)) + stT252 117 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 116
    simpa using h
  have hprev := st252_p116
  have hstep := st252_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p118 : ((30712560058983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT252 (i+1))
      = (∑ i ∈ Finset.range 117, stT252 (i+1)) + stT252 118 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 117
    simpa using h
  have hprev := st252_p117
  have hstep := st252_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p119 : ((30780497464461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT252 (i+1))
      = (∑ i ∈ Finset.range 118, stT252 (i+1)) + stT252 119 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 118
    simpa using h
  have hprev := st252_p118
  have hstep := st252_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p120 : ((31527508114161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT252 (i+1))
      = (∑ i ∈ Finset.range 119, stT252 (i+1)) + stT252 120 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 119
    simpa using h
  have hprev := st252_p119
  have hstep := st252_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p121 : ((30704208031831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT252 (i+1))
      = (∑ i ∈ Finset.range 120, stT252 (i+1)) + stT252 121 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 120
    simpa using h
  have hprev := st252_p120
  have hstep := st252_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p122 : ((1230527391901/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT252 (i+1))
      = (∑ i ∈ Finset.range 121, stT252 (i+1)) + stT252 122 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 121
    simpa using h
  have hprev := st252_p121
  have hstep := st252_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p123 : ((6306216436937/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT252 (i+1))
      = (∑ i ∈ Finset.range 122, stT252 (i+1)) + stT252 123 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 122
    simpa using h
  have hprev := st252_p122
  have hstep := st252_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p124 : ((30765214226167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT252 (i+1))
      = (∑ i ∈ Finset.range 123, stT252 (i+1)) + stT252 124 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 123
    simpa using h
  have hprev := st252_p123
  have hstep := st252_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p125 : ((30679270428503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT252 (i+1))
      = (∑ i ∈ Finset.range 124, stT252 (i+1)) + stT252 125 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 124
    simpa using h
  have hprev := st252_p124
  have hstep := st252_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p126 : ((31518798699533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT252 (i+1))
      = (∑ i ∈ Finset.range 125, stT252 (i+1)) + stT252 126 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 125
    simpa using h
  have hprev := st252_p125
  have hstep := st252_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p127 : ((30905961559909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT252 (i+1))
      = (∑ i ∈ Finset.range 126, stT252 (i+1)) + stT252 127 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 126
    simpa using h
  have hprev := st252_p126
  have hstep := st252_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p128 : ((30559427766637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT252 (i+1))
      = (∑ i ∈ Finset.range 127, stT252 (i+1)) + stT252 128 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 127
    simpa using h
  have hprev := st252_p127
  have hstep := st252_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p129 : ((31439765069037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT252 (i+1))
      = (∑ i ∈ Finset.range 128, stT252 (i+1)) + stT252 129 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 128
    simpa using h
  have hprev := st252_p128
  have hstep := st252_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p130 : ((15564290075271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT252 (i+1))
      = (∑ i ∈ Finset.range 129, stT252 (i+1)) + stT252 130 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 129
    simpa using h
  have hprev := st252_p129
  have hstep := st252_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p131 : ((15236678658831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT252 (i+1))
      = (∑ i ∈ Finset.range 130, stT252 (i+1)) + stT252 131 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 130
    simpa using h
  have hprev := st252_p130
  have hstep := st252_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p132 : ((15618089208341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT252 (i+1))
      = (∑ i ∈ Finset.range 131, stT252 (i+1)) + stT252 132 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 131
    simpa using h
  have hprev := st252_p131
  have hstep := st252_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p133 : ((31383884365069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT252 (i+1))
      = (∑ i ∈ Finset.range 132, stT252 (i+1)) + stT252 133 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 132
    simpa using h
  have hprev := st252_p132
  have hstep := st252_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p134 : ((6105823072223/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT252 (i+1))
      = (∑ i ∈ Finset.range 133, stT252 (i+1)) + stT252 134 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 133
    simpa using h
  have hprev := st252_p133
  have hstep := st252_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p135 : ((30902213198777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT252 (i+1))
      = (∑ i ∈ Finset.range 134, stT252 (i+1)) + stT252 135 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 134
    simpa using h
  have hprev := st252_p134
  have hstep := st252_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p136 : ((31536891905021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT252 (i+1))
      = (∑ i ∈ Finset.range 135, stT252 (i+1)) + stT252 136 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 135
    simpa using h
  have hprev := st252_p135
  have hstep := st252_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p137 : ((30812081917277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT252 (i+1))
      = (∑ i ∈ Finset.range 136, stT252 (i+1)) + stT252 137 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 136
    simpa using h
  have hprev := st252_p136
  have hstep := st252_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p138 : ((6112734300913/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT252 (i+1))
      = (∑ i ∈ Finset.range 137, stT252 (i+1)) + stT252 138 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 137
    simpa using h
  have hprev := st252_p137
  have hstep := st252_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p139 : ((31410866276417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT252 (i+1))
      = (∑ i ∈ Finset.range 138, stT252 (i+1)) + stT252 139 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 138
    simpa using h
  have hprev := st252_p138
  have hstep := st252_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p140 : ((3906576269689/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT252 (i+1))
      = (∑ i ∈ Finset.range 139, stT252 (i+1)) + stT252 140 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 139
    simpa using h
  have hprev := st252_p139
  have hstep := st252_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p141 : ((3810072808781/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT252 (i+1))
      = (∑ i ∈ Finset.range 140, stT252 (i+1)) + stT252 141 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 140
    simpa using h
  have hprev := st252_p140
  have hstep := st252_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p142 : ((30968979937981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT252 (i+1))
      = (∑ i ∈ Finset.range 141, stT252 (i+1)) + stT252 142 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 141
    simpa using h
  have hprev := st252_p141
  have hstep := st252_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p143 : ((31540125697803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT252 (i+1))
      = (∑ i ∈ Finset.range 142, stT252 (i+1)) + stT252 143 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 142
    simpa using h
  have hprev := st252_p142
  have hstep := st252_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p144 : ((30836986801959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT252 (i+1))
      = (∑ i ∈ Finset.range 143, stT252 (i+1)) + stT252 144 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 143
    simpa using h
  have hprev := st252_p143
  have hstep := st252_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p145 : ((15259280644517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT252 (i+1))
      = (∑ i ∈ Finset.range 144, stT252 (i+1)) + stT252 145 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 144
    simpa using h
  have hprev := st252_p144
  have hstep := st252_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p146 : ((31323897921299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT252 (i+1))
      = (∑ i ∈ Finset.range 145, stT252 (i+1)) + stT252 146 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 145
    simpa using h
  have hprev := st252_p145
  have hstep := st252_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p147 : ((31392196800387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT252 (i+1))
      = (∑ i ∈ Finset.range 146, stT252 (i+1)) + stT252 147 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 146
    simpa using h
  have hprev := st252_p146
  have hstep := st252_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p148 : ((30571392049147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT252 (i+1))
      = (∑ i ∈ Finset.range 147, stT252 (i+1)) + stT252 148 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 147
    simpa using h
  have hprev := st252_p147
  have hstep := st252_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p149 : ((30718768429123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT252 (i+1))
      = (∑ i ∈ Finset.range 148, stT252 (i+1)) + stT252 149 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 148
    simpa using h
  have hprev := st252_p148
  have hstep := st252_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p150 : ((1259991082539/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT252 (i+1))
      = (∑ i ∈ Finset.range 149, stT252 (i+1)) + stT252 150 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 149
    simpa using h
  have hprev := st252_p149
  have hstep := st252_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p151 : ((31183296148953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT252 (i+1))
      = (∑ i ∈ Finset.range 150, stT252 (i+1)) + stT252 151 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 150
    simpa using h
  have hprev := st252_p150
  have hstep := st252_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p152 : ((30468338513489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT252 (i+1))
      = (∑ i ∈ Finset.range 151, stT252 (i+1)) + stT252 152 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 151
    simpa using h
  have hprev := st252_p151
  have hstep := st252_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p153 : ((30907032056057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT252 (i+1))
      = (∑ i ∈ Finset.range 152, stT252 (i+1)) + stT252 153 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 152
    simpa using h
  have hprev := st252_p152
  have hstep := st252_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p154 : ((31551148143673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT252 (i+1))
      = (∑ i ∈ Finset.range 153, stT252 (i+1)) + stT252 154 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 153
    simpa using h
  have hprev := st252_p153
  have hstep := st252_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p155 : ((31030709776873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT252 (i+1))
      = (∑ i ∈ Finset.range 154, stT252 (i+1)) + stT252 155 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 154
    simpa using h
  have hprev := st252_p154
  have hstep := st252_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p156 : ((30447367548119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT252 (i+1))
      = (∑ i ∈ Finset.range 155, stT252 (i+1)) + stT252 156 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 155
    simpa using h
  have hprev := st252_p155
  have hstep := st252_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p157 : ((31016513001987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT252 (i+1))
      = (∑ i ∈ Finset.range 156, stT252 (i+1)) + stT252 157 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 156
    simpa using h
  have hprev := st252_p156
  have hstep := st252_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p158 : ((61635416887/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT252 (i+1))
      = (∑ i ∈ Finset.range 157, stT252 (i+1)) + stT252 158 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 157
    simpa using h
  have hprev := st252_p157
  have hstep := st252_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p159 : ((3870688212789/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT252 (i+1))
      = (∑ i ∈ Finset.range 158, stT252 (i+1)) + stT252 159 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 158
    simpa using h
  have hprev := st252_p158
  have hstep := st252_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p160 : ((3805574495879/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT252 (i+1))
      = (∑ i ∈ Finset.range 159, stT252 (i+1)) + stT252 160 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 159
    simpa using h
  have hprev := st252_p159
  have hstep := st252_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p161 : ((15518530011931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT252 (i+1))
      = (∑ i ∈ Finset.range 160, stT252 (i+1)) + stT252 161 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 160
    simpa using h
  have hprev := st252_p160
  have hstep := st252_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p162 : ((15780603359741/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT252 (i+1))
      = (∑ i ∈ Finset.range 161, stT252 (i+1)) + stT252 162 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 161
    simpa using h
  have hprev := st252_p161
  have hstep := st252_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p163 : ((7747073398519/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT252 (i+1))
      = (∑ i ∈ Finset.range 162, stT252 (i+1)) + stT252 163 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 162
    simpa using h
  have hprev := st252_p162
  have hstep := st252_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p164 : ((15219558117533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT252 (i+1))
      = (∑ i ∈ Finset.range 163, stT252 (i+1)) + stT252 164 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 163
    simpa using h
  have hprev := st252_p163
  have hstep := st252_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p165 : ((15485424526509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT252 (i+1))
      = (∑ i ∈ Finset.range 164, stT252 (i+1)) + stT252 165 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 164
    simpa using h
  have hprev := st252_p164
  have hstep := st252_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p166 : ((1972657781073/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT252 (i+1))
      = (∑ i ∈ Finset.range 165, stT252 (i+1)) + stT252 166 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 165
    simpa using h
  have hprev := st252_p165
  have hstep := st252_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p167 : ((1943518422709/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT252 (i+1))
      = (∑ i ∈ Finset.range 166, stT252 (i+1)) + stT252 167 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 166
    simpa using h
  have hprev := st252_p166
  have hstep := st252_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p168 : ((30451011060333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT252 (i+1))
      = (∑ i ∈ Finset.range 167, stT252 (i+1)) + stT252 168 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 167
    simpa using h
  have hprev := st252_p167
  have hstep := st252_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p169 : ((30823138380513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT252 (i+1))
      = (∑ i ∈ Finset.range 168, stT252 (i+1)) + stT252 169 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 168
    simpa using h
  have hprev := st252_p168
  have hstep := st252_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p170 : ((31523112676897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT252 (i+1))
      = (∑ i ∈ Finset.range 169, stT252 (i+1)) + stT252 170 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 169
    simpa using h
  have hprev := st252_p169
  have hstep := st252_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p171 : ((31276613596817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT252 (i+1))
      = (∑ i ∈ Finset.range 170, stT252 (i+1)) + stT252 171 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 170
    simpa using h
  have hprev := st252_p170
  have hstep := st252_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p172 : ((15266799240251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT252 (i+1))
      = (∑ i ∈ Finset.range 171, stT252 (i+1)) + stT252 172 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 171
    simpa using h
  have hprev := st252_p171
  have hstep := st252_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p173 : ((30622167881577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT252 (i+1))
      = (∑ i ∈ Finset.range 172, stT252 (i+1)) + stT252 173 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 172
    simpa using h
  have hprev := st252_p172
  have hstep := st252_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p174 : ((31380227218579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT252 (i+1))
      = (∑ i ∈ Finset.range 173, stT252 (i+1)) + stT252 174 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 173
    simpa using h
  have hprev := st252_p173
  have hstep := st252_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p175 : ((31476829525483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT252 (i+1))
      = (∑ i ∈ Finset.range 174, stT252 (i+1)) + stT252 175 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 174
    simpa using h
  have hprev := st252_p174
  have hstep := st252_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p176 : ((30748950371923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT252 (i+1))
      = (∑ i ∈ Finset.range 175, stT252 (i+1)) + stT252 176 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 175
    simpa using h
  have hprev := st252_p175
  have hstep := st252_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p177 : ((15225992206817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT252 (i+1))
      = (∑ i ∈ Finset.range 176, stT252 (i+1)) + stT252 177 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 176
    simpa using h
  have hprev := st252_p176
  have hstep := st252_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p178 : ((3108810837521/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT252 (i+1))
      = (∑ i ∈ Finset.range 177, stT252 (i+1)) + stT252 178 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 177
    simpa using h
  have hprev := st252_p177
  have hstep := st252_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p179 : ((3157878151427/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT252 (i+1))
      = (∑ i ∈ Finset.range 178, stT252 (i+1)) + stT252 179 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 178
    simpa using h
  have hprev := st252_p178
  have hstep := st252_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p180 : ((15552814017379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT252 (i+1))
      = (∑ i ∈ Finset.range 179, stT252 (i+1)) + stT252 180 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 179
    simpa using h
  have hprev := st252_p179
  have hstep := st252_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p181 : ((30457983951833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT252 (i+1))
      = (∑ i ∈ Finset.range 180, stT252 (i+1)) + stT252 181 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 180
    simpa using h
  have hprev := st252_p180
  have hstep := st252_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p182 : ((1534929780049/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT252 (i+1))
      = (∑ i ∈ Finset.range 181, stT252 (i+1)) + stT252 182 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 181
    simpa using h
  have hprev := st252_p181
  have hstep := st252_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p183 : ((31430476875671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT252 (i+1))
      = (∑ i ∈ Finset.range 182, stT252 (i+1)) + stT252 183 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 182
    simpa using h
  have hprev := st252_p182
  have hstep := st252_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p184 : ((31472301691077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT252 (i+1))
      = (∑ i ∈ Finset.range 183, stT252 (i+1)) + stT252 184 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 183
    simpa using h
  have hprev := st252_p183
  have hstep := st252_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p185 : ((30762091353227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT252 (i+1))
      = (∑ i ∈ Finset.range 184, stT252 (i+1)) + stT252 185 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 184
    simpa using h
  have hprev := st252_p184
  have hstep := st252_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p186 : ((30427330257719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT252 (i+1))
      = (∑ i ∈ Finset.range 185, stT252 (i+1)) + stT252 186 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 185
    simpa using h
  have hprev := st252_p185
  have hstep := st252_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p187 : ((30989589941807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT252 (i+1))
      = (∑ i ∈ Finset.range 186, stT252 (i+1)) + stT252 187 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 186
    simpa using h
  have hprev := st252_p186
  have hstep := st252_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p188 : ((6313999675903/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT252 (i+1))
      = (∑ i ∈ Finset.range 187, stT252 (i+1)) + stT252 188 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 187
    simpa using h
  have hprev := st252_p187
  have hstep := st252_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p189 : ((31275721357863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT252 (i+1))
      = (∑ i ∈ Finset.range 188, stT252 (i+1)) + stT252 189 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 188
    simpa using h
  have hprev := st252_p188
  have hstep := st252_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p190 : ((15280673166197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT252 (i+1))
      = (∑ i ∈ Finset.range 189, stT252 (i+1)) + stT252 190 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 189
    simpa using h
  have hprev := st252_p189
  have hstep := st252_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p191 : ((30508902339969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT252 (i+1))
      = (∑ i ∈ Finset.range 190, stT252 (i+1)) + stT252 191 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 190
    simpa using h
  have hprev := st252_p190
  have hstep := st252_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p192 : ((487378518449/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT252 (i+1))
      = (∑ i ∈ Finset.range 191, stT252 (i+1)) + stT252 192 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 191
    simpa using h
  have hprev := st252_p191
  have hstep := st252_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p193 : ((31592113365281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT252 (i+1))
      = (∑ i ∈ Finset.range 192, stT252 (i+1)) + stT252 193 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 192
    simpa using h
  have hprev := st252_p192
  have hstep := st252_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p194 : ((31122315457713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT252 (i+1))
      = (∑ i ∈ Finset.range 193, stT252 (i+1)) + stT252 194 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 193
    simpa using h
  have hprev := st252_p193
  have hstep := st252_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p195 : ((952306057389/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT252 (i+1))
      = (∑ i ∈ Finset.range 194, stT252 (i+1)) + stT252 195 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 194
    simpa using h
  have hprev := st252_p194
  have hstep := st252_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p196 : ((30584950153863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT252 (i+1))
      = (∑ i ∈ Finset.range 195, stT252 (i+1)) + stT252 196 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 195
    simpa using h
  have hprev := st252_p195
  have hstep := st252_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p197 : ((31291183191483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT252 (i+1))
      = (∑ i ∈ Finset.range 196, stT252 (i+1)) + stT252 197 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 196
    simpa using h
  have hprev := st252_p196
  have hstep := st252_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p198 : ((3948173687181/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT252 (i+1))
      = (∑ i ∈ Finset.range 197, stT252 (i+1)) + stT252 198 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 197
    simpa using h
  have hprev := st252_p197
  have hstep := st252_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p199 : ((15528120492069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT252 (i+1))
      = (∑ i ∈ Finset.range 198, stT252 (i+1)) + stT252 199 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 198
    simpa using h
  have hprev := st252_p198
  have hstep := st252_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p200 : ((30447901982791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT252 (i+1))
      = (∑ i ∈ Finset.range 199, stT252 (i+1)) + stT252 200 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 199
    simpa using h
  have hprev := st252_p199
  have hstep := st252_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p201 : ((7650633515449/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT252 (i+1))
      = (∑ i ∈ Finset.range 200, stT252 (i+1)) + stT252 201 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 200
    simpa using h
  have hprev := st252_p200
  have hstep := st252_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p202 : ((3130264262787/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT252 (i+1))
      = (∑ i ∈ Finset.range 201, stT252 (i+1)) + stT252 202 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 201
    simpa using h
  have hprev := st252_p201
  have hstep := st252_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p203 : ((789807439149/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT252 (i+1))
      = (∑ i ∈ Finset.range 202, stT252 (i+1)) + stT252 203 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 202
    simpa using h
  have hprev := st252_p202
  have hstep := st252_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p204 : ((7770944889133/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT252 (i+1))
      = (∑ i ∈ Finset.range 203, stT252 (i+1)) + stT252 204 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 203
    simpa using h
  have hprev := st252_p203
  have hstep := st252_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p205 : ((3046242600483/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT252 (i+1))
      = (∑ i ∈ Finset.range 204, stT252 (i+1)) + stT252 205 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 204
    simpa using h
  have hprev := st252_p204
  have hstep := st252_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p206 : ((119346077329/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT252 (i+1))
      = (∑ i ∈ Finset.range 205, stT252 (i+1)) + stT252 206 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 205
    simpa using h
  have hprev := st252_p205
  have hstep := st252_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p207 : ((1951922567519/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT252 (i+1))
      = (∑ i ∈ Finset.range 206, stT252 (i+1)) + stT252 207 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 206
    simpa using h
  have hprev := st252_p206
  have hstep := st252_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p208 : ((15804474303277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT252 (i+1))
      = (∑ i ∈ Finset.range 207, stT252 (i+1)) + stT252 208 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 207
    simpa using h
  have hprev := st252_p207
  have hstep := st252_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p209 : ((15600227464937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT252 (i+1))
      = (∑ i ∈ Finset.range 208, stT252 (i+1)) + stT252 209 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 208
    simpa using h
  have hprev := st252_p208
  have hstep := st252_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p210 : ((15267109144493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT252 (i+1))
      = (∑ i ∈ Finset.range 209, stT252 (i+1)) + stT252 210 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 209
    simpa using h
  have hprev := st252_p209
  have hstep := st252_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p211 : ((7614671308991/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT252 (i+1))
      = (∑ i ∈ Finset.range 210, stT252 (i+1)) + stT252 211 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 210
    simpa using h
  have hprev := st252_p210
  have hstep := st252_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p212 : ((15532447914439/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT252 (i+1))
      = (∑ i ∈ Finset.range 211, stT252 (i+1)) + stT252 212 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 211
    simpa using h
  have hprev := st252_p211
  have hstep := st252_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p213 : ((15795191817889/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT252 (i+1))
      = (∑ i ∈ Finset.range 212, stT252 (i+1)) + stT252 213 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 212
    simpa using h
  have hprev := st252_p212
  have hstep := st252_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p214 : ((7846068050747/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT252 (i+1))
      = (∑ i ∈ Finset.range 213, stT252 (i+1)) + stT252 214 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 213
    simpa using h
  have hprev := st252_p213
  have hstep := st252_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p215 : ((15352493725559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT252 (i+1))
      = (∑ i ∈ Finset.range 214, stT252 (i+1)) + stT252 215 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 214
    simpa using h
  have hprev := st252_p214
  have hstep := st252_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p216 : ((15192018764073/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT252 (i+1))
      = (∑ i ∈ Finset.range 215, stT252 (i+1)) + stT252 216 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 215
    simpa using h
  have hprev := st252_p215
  have hstep := st252_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p217 : ((15403523473777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT252 (i+1))
      = (∑ i ∈ Finset.range 216, stT252 (i+1)) + stT252 217 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 216
    simpa using h
  have hprev := st252_p216
  have hstep := st252_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p218 : ((7865356203571/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT252 (i+1))
      = (∑ i ∈ Finset.range 217, stT252 (i+1)) + stT252 218 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 217
    simpa using h
  have hprev := st252_p217
  have hstep := st252_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p219 : ((31566939119623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT252 (i+1))
      = (∑ i ∈ Finset.range 218, stT252 (i+1)) + stT252 219 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 218
    simpa using h
  have hprev := st252_p218
  have hstep := st252_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p220 : ((31002804966423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT252 (i+1))
      = (∑ i ∈ Finset.range 219, stT252 (i+1)) + stT252 220 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 219
    simpa using h
  have hprev := st252_p219
  have hstep := st252_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p221 : ((30434026311273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT252 (i+1))
      = (∑ i ∈ Finset.range 220, stT252 (i+1)) + stT252 221 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 220
    simpa using h
  have hprev := st252_p220
  have hstep := st252_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p222 : ((30521116184989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT252 (i+1))
      = (∑ i ∈ Finset.range 221, stT252 (i+1)) + stT252 222 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 221
    simpa using h
  have hprev := st252_p221
  have hstep := st252_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p223 : ((486862708329/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT252 (i+1))
      = (∑ i ∈ Finset.range 222, stT252 (i+1)) + stT252 223 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 222
    simpa using h
  have hprev := st252_p222
  have hstep := st252_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p224 : ((7903813620419/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT252 (i+1))
      = (∑ i ∈ Finset.range 223, stT252 (i+1)) + stT252 224 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 223
    simpa using h
  have hprev := st252_p223
  have hstep := st252_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p225 : ((31373393694079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT252 (i+1))
      = (∑ i ∈ Finset.range 224, stT252 (i+1)) + stT252 225 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 224
    simpa using h
  have hprev := st252_p224
  have hstep := st252_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p226 : ((15355204566313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT252 (i+1))
      = (∑ i ∈ Finset.range 225, stT252 (i+1)) + stT252 226 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 225
    simpa using h
  have hprev := st252_p225
  have hstep := st252_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p227 : ((15184484465791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT252 (i+1))
      = (∑ i ∈ Finset.range 226, stT252 (i+1)) + stT252 227 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 226
    simpa using h
  have hprev := st252_p226
  have hstep := st252_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p228 : ((15362434015459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT252 (i+1))
      = (∑ i ∈ Finset.range 227, stT252 (i+1)) + stT252 228 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 227
    simpa using h
  have hprev := st252_p227
  have hstep := st252_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p229 : ((15691193613731/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT252 (i+1))
      = (∑ i ∈ Finset.range 228, stT252 (i+1)) + stT252 229 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 228
    simpa using h
  have hprev := st252_p228
  have hstep := st252_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p230 : ((15811410456571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT252 (i+1))
      = (∑ i ∈ Finset.range 229, stT252 (i+1)) + stT252 230 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 229
    simpa using h
  have hprev := st252_p229
  have hstep := st252_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p231 : ((623779070947/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT252 (i+1))
      = (∑ i ∈ Finset.range 230, stT252 (i+1)) + stT252 231 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 230
    simpa using h
  have hprev := st252_p230
  have hstep := st252_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p232 : ((3818856506849/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT252 (i+1))
      = (∑ i ∈ Finset.range 231, stT252 (i+1)) + stT252 232 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 231
    simpa using h
  have hprev := st252_p231
  have hstep := st252_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p233 : ((15194625572843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT252 (i+1))
      = (∑ i ∈ Finset.range 232, stT252 (i+1)) + stT252 233 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 232
    simpa using h
  have hprev := st252_p232
  have hstep := st252_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p234 : ((15435819489163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT252 (i+1))
      = (∑ i ∈ Finset.range 233, stT252 (i+1)) + stT252 234 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 233
    simpa using h
  have hprev := st252_p233
  have hstep := st252_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p235 : ((3148791150511/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT252 (i+1))
      = (∑ i ∈ Finset.range 234, stT252 (i+1)) + stT252 235 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 234
    simpa using h
  have hprev := st252_p234
  have hstep := st252_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p236 : ((15797992892299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT252 (i+1))
      = (∑ i ∈ Finset.range 235, stT252 (i+1)) + stT252 236 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 235
    simpa using h
  have hprev := st252_p235
  have hstep := st252_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p237 : ((15543830441839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT252 (i+1))
      = (∑ i ∈ Finset.range 236, stT252 (i+1)) + stT252 237 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 236
    simpa using h
  have hprev := st252_p236
  have hstep := st252_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p238 : ((15243917794609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT252 (i+1))
      = (∑ i ∈ Finset.range 237, stT252 (i+1)) + stT252 238 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 237
    simpa using h
  have hprev := st252_p237
  have hstep := st252_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p239 : ((30406994591699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT252 (i+1))
      = (∑ i ∈ Finset.range 238, stT252 (i+1)) + stT252 239 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 238
    simpa using h
  have hprev := st252_p238
  have hstep := st252_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p240 : ((3865403125997/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT252 (i+1))
      = (∑ i ∈ Finset.range 239, stT252 (i+1)) + stT252 240 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 239
    simpa using h
  have hprev := st252_p239
  have hstep := st252_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p241 : ((1575775001979/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT252 (i+1))
      = (∑ i ∈ Finset.range 240, stT252 (i+1)) + stT252 241 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 240
    simpa using h
  have hprev := st252_p240
  have hstep := st252_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p242 : ((7898639598011/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT252 (i+1))
      = (∑ i ∈ Finset.range 241, stT252 (i+1)) + stT252 242 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 241
    simpa using h
  have hprev := st252_p241
  have hstep := st252_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p243 : ((31085774326429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT252 (i+1))
      = (∑ i ∈ Finset.range 242, stT252 (i+1)) + stT252 243 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 242
    simpa using h
  have hprev := st252_p242
  have hstep := st252_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p244 : ((7622802707521/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT252 (i+1))
      = (∑ i ∈ Finset.range 243, stT252 (i+1)) + stT252 244 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 243
    simpa using h
  have hprev := st252_p243
  have hstep := st252_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p245 : ((15194637724613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT252 (i+1))
      = (∑ i ∈ Finset.range 244, stT252 (i+1)) + stT252 245 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 244
    simpa using h
  have hprev := st252_p244
  have hstep := st252_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p246 : ((15437517519993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT252 (i+1))
      = (∑ i ∈ Finset.range 245, stT252 (i+1)) + stT252 246 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 245
    simpa using h
  have hprev := st252_p245
  have hstep := st252_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p247 : ((629588455187/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT252 (i+1))
      = (∑ i ∈ Finset.range 246, stT252 (i+1)) + stT252 247 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 246
    simpa using h
  have hprev := st252_p246
  have hstep := st252_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p248 : ((632542487887/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT252 (i+1))
      = (∑ i ∈ Finset.range 247, stT252 (i+1)) + stT252 248 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 247
    simpa using h
  have hprev := st252_p247
  have hstep := st252_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p249 : ((249453883947/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT252 (i+1))
      = (∑ i ∈ Finset.range 248, stT252 (i+1)) + stT252 249 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 248
    simpa using h
  have hprev := st252_p248
  have hstep := st252_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_p250 : ((6112857534851/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT252 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT252 (i+1))
      = (∑ i ∈ Finset.range 249, stT252 (i+1)) + stT252 250 := by
    have h := Finset.sum_range_succ (fun i => stT252 (i+1)) 249
    simpa using h
  have hprev := st252_p249
  have hstep := st252_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st252_s250 :
    |Real.sin (((252 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))
      - ((-216781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -1826923/2500000) (δ := 197/15625000) (ψ := -267951/500000) 252 222
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 252`** (evaluated boundary). -/
theorem station_252_sign : 0 < hardyG ((((252:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 252 250 (by norm_num) (by norm_num)
    ((-267951/500000 : ℚ) : ℝ)
  have hchain := st252_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT252 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((252 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-267951/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st252_c250
  have hsinb := abs_le.mp st252_s250
  have hbdy_lo : ((6970197631827/508034000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((252 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-267951/500000 : ℚ) : ℝ))) / 2
          - ((((252:ℕ)):ℝ))
            * Real.sin (((252 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-267951/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((252:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((252:ℝ) * Real.log (250:ℝ) - ((-267951/500000 : ℚ) : ℝ))) / 2
        - ((252:ℝ)) * Real.sin ((252:ℝ) * Real.log (250:ℝ) - ((-267951/500000 : ℚ) : ℝ))
        ≥ ((55104297/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((252:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((55104297/1000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((55104297/1000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((55104297/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((252:ℕ)):ℝ))+1) * (((((252:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((1307357149901/937500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((6112857534851/2000000000000 : ℚ) : ℝ) + ((6970197631827/508034000000000 : ℚ) : ℝ)
      - ((1307357149901/937500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-267951/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((252:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-267951/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((252:ℕ)):ℝ)))).re
      - Real.sin ((-267951/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((252:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((252:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((252:ℕ)):ℝ))
      = (((((252:ℕ)):ℝ)) * (Real.log ((((252:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((252:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_252
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
  have hθwin : |(((-267951/500000 : ℚ) : ℝ) + ((54:ℤ)) * (2*Real.pi)) - theta ((((252:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((252:ℕ)):ℝ)))
    (φ := ((-267951/500000 : ℚ) : ℝ) + ((54:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-267951/500000 : ℚ)) : ℝ) 54).1,
    (cos_sin_shift (((-267951/500000 : ℚ)) : ℝ) 54).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_252_sign
end AxiomAudit
