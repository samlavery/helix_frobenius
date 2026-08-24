import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 128` (rung-144.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT128 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((128 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-8717/31250 : ℚ) : ℝ))

theorem st128_c1 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((961347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8717/125000) (δ := 1/1000000000) (ψ := -8717/31250) 128 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t1 : ((961297/1000000 : ℚ) : ℝ) ≤ stT128 1 := by
  have hc : ((961297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((961297/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((961297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c2 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((254323/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1296481/5000000) (δ := 6501/1000000000) (ψ := -8717/31250) 128 14
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t2 : ((899079097983/2500000000000 : ℚ) : ℝ) ≤ stT128 2 := by
  have hc : ((127149/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((899079097983/2500000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((127149/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c3 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-445703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 834761/1250000) (δ := 1611/250000000) (ψ := -8717/31250) 128 22
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t3 : ((-80419123287/156250000000 : ℚ) : ℝ) ≤ stT128 3 := by
  have hc : ((-13929/15625 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80419123287/156250000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-13929/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c4 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-222751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 224429/500000) (δ := 33/5000000) (ψ := -8717/31250) 128 28
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t4 : ((-1114005222801/10000000000000 : ℚ) : ℝ) ≤ stT128 4 := by
  have hc : ((-222801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1114005222801/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-222801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c5 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((490517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -661321/2500000) (δ := 1293/200000000) (ψ := -8717/31250) 128 33
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t5 : ((438686927409/2000000000000 : ℚ) : ℝ) ≤ stT128 5 := by
  have hc : ((490467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((438686927409/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((490467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c6 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-191769/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7134257/10000000) (δ := 1609/250000000) (ψ := -8717/31250) 128 37
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t6 : ((-782934507257/2000000000000 : ℚ) : ℝ) ≤ stT128 6 := by
  have hc : ((-191779/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-782934507257/2000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-191779/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c7 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-195249/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4929923/10000000) (δ := 3257/500000000) (ψ := -8717/31250) 128 40
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t7 : ((-73806639773/500000000000 : ℚ) : ℝ) ≤ stT128 7 := by
  have hc : ((-97637/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73806639773/500000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-97637/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c8 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-8321/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6384199/10000000) (δ := 6503/1000000000) (ψ := -8717/31250) 128 42
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t8 : ((-29420946181/100000000000 : ℚ) : ℝ) ≤ stT128 8 := by
  have hc : ((-16643/20000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29420946181/100000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-16643/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c9 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((85993/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3049131/10000000) (δ := 257/40000000) (ψ := -8717/31250) 128 45
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t9 : ((573203276013/5000000000000 : ℚ) : ℝ) ≤ stT128 9 := by
  have hc : ((171961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((573203276013/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((171961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c10 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((238843/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -374849/5000000) (δ := 1641/250000000) (ψ := -8717/31250) 128 47
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t10 : ((1510496394097/5000000000000 : ℚ) : ℝ) ≤ stT128 10 := by
  have hc : ((477661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1510496394097/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((477661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c11 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((785963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41659/250000) (δ := 6453/1000000000) (ψ := -8717/31250) 128 49
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t11 : ((2369616503169/10000000000000 : ℚ) : ℝ) ≤ stT128 11 := by
  have hc : ((785913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2369616503169/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((785913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c12 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-250459/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5238639/10000000) (δ := 1307/200000000) (ψ := -8717/31250) 128 51
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t12 : ((-5649103031/39062500000 : ℚ) : ℝ) ≤ stT128 12 := by
  have hc : ((-62621/125000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5649103031/39062500000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-62621/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c13 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-72931/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2333531/5000000) (δ := 1607/250000000) (ψ := -8717/31250) 128 52
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t13 : ((-404617740387/5000000000000 : ℚ) : ℝ) ≤ stT128 13 := by
  have hc : ((-145887/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-404617740387/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-145887/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c14 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((69907/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47411/156250) (δ := 6589/1000000000) (ψ := -8717/31250) 128 54
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t14 : ((46701890241/500000000000 : ℚ) : ℝ) ≤ stT128 14 := by
  have hc : ((69897/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46701890241/500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((69897/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c15 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((234411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 166773/500000) (δ := 6507/1000000000) (ψ := -8717/31250) 128 55
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t15 : ((151279322417/2500000000000 : ℚ) : ℝ) ≤ stT128 15 := by
  have hc : ((234361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151279322417/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((234361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c16 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-123191/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3714073/5000000) (δ := 6511/1000000000) (ψ := -8717/31250) 128 57
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t16 : ((-1231972992789/5000000000000 : ℚ) : ℝ) ≤ stT128 16 := by
  have hc : ((-492789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1231972992789/5000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-492789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c17 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((76227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1868119/5000000) (δ := 1317/200000000) (ψ := -8717/31250) 128 58
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t17 : ((46189086003/2500000000000 : ℚ) : ℝ) ≤ stT128 17 := by
  have hc : ((76177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46189086003/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((76177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c18 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((223857/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1153513/10000000) (δ := 3239/500000000) (ψ := -8717/31250) 128 59
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t18 : ((527606411079/2500000000000 : ℚ) : ℝ) ≤ stT128 18 := by
  have hc : ((447689/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((527606411079/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((447689/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c19 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((19691/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 110007/2500000) (δ := 201/31250000) (ψ := -8717/31250) 128 60
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t19 : ((4517195133/20000000000 : ℚ) : ℝ) ≤ stT128 19 := by
  have hc : ((1969/2000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4517195133/20000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((1969/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c20 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((112097/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1145921/10000000) (δ := 6539/1000000000) (ψ := -8717/31250) 128 61
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t20 : ((1002569708321/5000000000000 : ℚ) : ℝ) ≤ stT128 20 := by
  have hc : ((448363/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1002569708321/5000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((448363/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c21 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((182591/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1050821/10000000) (δ := 1639/250000000) (ψ := -8717/31250) 128 62
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t21 : ((199212120709/1000000000000 : ℚ) : ℝ) ≤ stT128 21 := by
  have hc : ((182581/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199212120709/1000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((182581/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c22 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((497899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 114629/5000000) (δ := 6449/1000000000) (ψ := -8717/31250) 128 63
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t22 : ((530735426559/2500000000000 : ℚ) : ℝ) ≤ stT128 22 := by
  have hc : ((248937/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((530735426559/2500000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((248937/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c23 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((87679/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1254129/10000000) (δ := 6461/1000000000) (ψ := -8717/31250) 128 64
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t23 : ((11425807191/62500000000 : ℚ) : ℝ) ≤ stT128 23 := by
  have hc : ((43837/50000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11425807191/62500000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((43837/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c24 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((23147/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -167151/500000) (δ := 821/125000000) (ψ := -8717/31250) 128 65
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t24 : ((23619199611/500000000000 : ℚ) : ℝ) ≤ stT128 24 := by
  have hc : ((11571/50000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23619199611/500000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((11571/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c25 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-45883/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -748493/1250000) (δ := 51/7812500) (ψ := -8717/31250) 128 66
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t25 : ((-734178367089/5000000000000 : ℚ) : ℝ) ≤ stT128 25 := by
  have hc : ((-367089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-734178367089/5000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-367089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c26 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-869543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 164067/250000) (δ := 51/7812500) (ψ := -8717/31250) 128 66
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t26 : ((-852706373533/5000000000000 : ℚ) : ℝ) ≤ stT128 26 := by
  have hc : ((-869593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-852706373533/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-869593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c27 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((77543/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2931613/10000000) (δ := 321/50000000) (ψ := -8717/31250) 128 67
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t27 : ((298424517/4000000000 : ℚ) : ℝ) ≤ stT128 27 := by
  have hc : ((77533/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298424517/4000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((77533/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c28 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((224513/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -569343/5000000) (δ := 649/100000000) (ψ := -8717/31250) 128 68
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t28 : ((424265983911/2500000000000 : ℚ) : ℝ) ≤ stT128 28 := by
  have hc : ((449001/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((424265983911/2500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((449001/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c29 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-78227/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5617433/10000000) (δ := 6597/1000000000) (ψ := -8717/31250) 128 69
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t29 : ((-290551093041/2500000000000 : ℚ) : ℝ) ≤ stT128 29 := by
  have hc : ((-312933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-290551093041/2500000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-312933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c30 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-498287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5231047/10000000) (δ := 6597/1000000000) (ψ := -8717/31250) 128 69
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t30 : ((-454917395527/5000000000000 : ℚ) : ℝ) ≤ stT128 30 := by
  have hc : ((-498337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-454917395527/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-498337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c31 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((49999/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15851/10000000) (δ := 6499/1000000000) (ψ := -8717/31250) 128 70
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t31 : ((179592727629/1000000000000 : ℚ) : ℝ) ≤ stT128 31 := by
  have hc : ((99993/100000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179592727629/1000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((99993/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c32 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-598971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -345783/625000) (δ := 6411/1000000000) (ψ := -8717/31250) 128 71
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t32 : ((-1058929556107/10000000000000 : ℚ) : ℝ) ≤ stT128 32 := by
  have hc : ((-599021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1058929556107/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-599021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c33 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-77169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 269649/625000) (δ := 6411/1000000000) (ψ := -8717/31250) 128 71
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t33 : ((-67188769869/2500000000000 : ℚ) : ℝ) ≤ stT128 33 := by
  have hc : ((-38597/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67188769869/2500000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-38597/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c34 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((370497/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1840619/10000000) (δ := 3259/500000000) (ψ := -8717/31250) 128 72
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t34 : ((15883848073/125000000000 : ℚ) : ℝ) ≤ stT128 34 := by
  have hc : ((46309/62500 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15883848073/125000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((46309/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c35 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-197203/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7435381/10000000) (δ := 3259/500000000) (ψ := -8717/31250) 128 72
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t35 : ((-333350908817/2000000000000 : ℚ) : ℝ) ≤ stT128 35 := by
  have hc : ((-197213/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333350908817/2000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-197213/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c36 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((191253/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 148421/2000000) (δ := 6577/1000000000) (ψ := -8717/31250) 128 73
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t36 : ((159369102919/1000000000000 : ℚ) : ℝ) ≤ stT128 36 := by
  have hc : ((191243/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159369102919/1000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((191243/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c37 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-788567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3099089/5000000) (δ := 647/100000000) (ψ := -8717/31250) 128 74
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t37 : ((-129647846183/1000000000000 : ℚ) : ℝ) ≤ stT128 37 := by
  have hc : ((-788617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129647846183/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-788617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c38 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((118883/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1167823/5000000) (δ := 647/100000000) (ψ := -8717/31250) 128 74
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t38 : ((96418722411/1000000000000 : ℚ) : ℝ) ≤ stT128 38 := by
  have hc : ((118873/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96418722411/1000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((118873/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c39 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-27369/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5060157/10000000) (δ := 161/25000000) (ψ := -8717/31250) 128 75
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t39 : ((-175321964257/2500000000000 : ℚ) : ℝ) ≤ stT128 39 := by
  have hc : ((-218977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175321964257/2500000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-218977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c40 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((173411/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3041539/10000000) (δ := 161/25000000) (ψ := -8717/31250) 128 75
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t40 : ((68536798317/1250000000000 : ℚ) : ℝ) ≤ stT128 40 := by
  have hc : ((86693/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68536798317/1250000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((86693/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c41 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-328883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -595599/1250000) (δ := 6547/1000000000) (ψ := -8717/31250) 128 76
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t41 : ((-256853582777/5000000000000 : ℚ) : ℝ) ≤ stT128 41 := by
  have hc : ((-328933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-256853582777/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-328933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c42 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((382241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73661/250000) (δ := 6547/1000000000) (ψ := -8717/31250) 128 76
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t42 : ((589733325303/10000000000000 : ℚ) : ℝ) ≤ stT128 42 := by
  have hc : ((382191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((589733325303/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((382191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c43 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-62317/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1307941/2500000) (δ := 6549/1000000000) (ψ := -8717/31250) 128 77
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t43 : ((-190084167449/2500000000000 : ℚ) : ℝ) ≤ stT128 43 := by
  have hc : ((-249293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190084167449/2500000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-249293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c44 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((33001/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 531219/2500000) (δ := 6549/1000000000) (ψ := -8717/31250) 128 77
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t44 : ((24873543333/250000000000 : ℚ) : ℝ) ≤ stT128 44 := by
  have hc : ((65997/100000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24873543333/250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((65997/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c45 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-41689/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6391791/10000000) (δ := 6441/1000000000) (ψ := -8717/31250) 128 78
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t45 : ((-15537504837/125000000000 : ℚ) : ℝ) ≤ stT128 45 := by
  have hc : ((-83383/100000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15537504837/125000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-83383/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c46 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((967263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 641457/10000000) (δ := 6441/1000000000) (ψ := -8717/31250) 128 78
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t46 : ((1426077224247/10000000000000 : ℚ) : ℝ) ≤ stT128 46 := by
  have hc : ((967213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1426077224247/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((967213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c47 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-495637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7523473/10000000) (δ := 6441/1000000000) (ψ := -8717/31250) 128 78
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t47 : ((-7229973763/50000000000 : ℚ) : ℝ) ≤ stT128 47 := by
  have hc : ((-247831/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7229973763/50000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-247831/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c48 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((104629/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -723701/5000000) (δ := 6469/1000000000) (ψ := -8717/31250) 128 79
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t48 : ((4832315577/40000000000 : ℚ) : ℝ) ≤ stT128 48 := by
  have hc : ((418491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4832315577/40000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((418491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c49 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-94037/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2575371/5000000) (δ := 6469/1000000000) (ψ := -8717/31250) 128 79
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t49 : ((-33588227721/500000000000 : ℚ) : ℝ) ≤ stT128 49 := by
  have hc : ((-94047/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33588227721/500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-94047/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c50 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-13217/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -163693/400000) (δ := 411/62500000) (ψ := -8717/31250) 128 80
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t50 : ((-9352904289/1000000000000 : ℚ) : ℝ) ≤ stT128 50 := by
  have hc : ((-13227/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9352904289/1000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-13227/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c51 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((62333/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2244507/10000000) (δ := 411/62500000) (ψ := -8717/31250) 128 80
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t51 : ((272739537/3125000000 : ℚ) : ℝ) ≤ stT128 51 := by
  have hc : ((7791/12500 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272739537/3125000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((7791/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c52 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-485463/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1449933/2000000) (δ := 163/25000000) (ψ := -8717/31250) 128 81
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t52 : ((-42078185593/312500000000 : ℚ) : ℝ) ≤ stT128 52 := by
  have hc : ((-30343/31250 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42078185593/312500000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-30343/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c53 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((447649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1154241/10000000) (δ := 163/25000000) (ψ := -8717/31250) 128 81
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t53 : ((15371464113/125000000000 : ℚ) : ℝ) ≤ stT128 53 := by
  have hc : ((55953/62500 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15371464113/125000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((55953/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c54 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-88091/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4827231/10000000) (δ := 163/25000000) (ψ := -8717/31250) 128 81
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t54 : ((-59946854849/1250000000000 : ℚ) : ℝ) ≤ stT128 54 := by
  have hc : ((-176207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59946854849/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-176207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c55 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-16777/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -250451/500000) (δ := 6413/1000000000) (ψ := -8717/31250) 128 82
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t55 : ((-56562009/1000000000 : ℚ) : ℝ) ≤ stT128 55 := by
  have hc : ((-16779/40000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56562009/1000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-16779/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c56 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((954517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7569/100000) (δ := 6413/1000000000) (ψ := -8717/31250) 128 82
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t56 : ((637729989451/5000000000000 : ℚ) : ℝ) ≤ stT128 56 := by
  have hc : ((954467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((637729989451/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((954467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c57 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-210031/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1605193/2500000) (δ := 6413/1000000000) (ψ := -8717/31250) 128 82
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t57 : ((-556419094371/5000000000000 : ℚ) : ℝ) ≤ stT128 57 := by
  have hc : ((-420087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-556419094371/5000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-420087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c58 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((40989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -744363/2000000) (δ := 6497/1000000000) (ψ := -8717/31250) 128 83
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t58 : ((1680886053/156250000000 : ℚ) : ℝ) ≤ stT128 58 := by
  have hc : ((10241/125000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1680886053/156250000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((10241/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c59 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((95657/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1748393/10000000) (δ := 6497/1000000000) (ψ := -8717/31250) 128 83
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t59 : ((498106637067/5000000000000 : ℚ) : ℝ) ≤ stT128 59 := by
  have hc : ((382603/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((498106637067/5000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((382603/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c60 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-478989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1425333/2000000) (δ := 6497/1000000000) (ψ := -8717/31250) 128 83
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t60 : ((-61840467893/500000000000 : ℚ) : ℝ) ≤ stT128 60 := by
  have hc : ((-239507/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61840467893/500000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-239507/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c61 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((31413/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3291923/10000000) (δ := 3299/500000000) (ψ := -8717/31250) 128 84
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t61 : ((10053049421/312500000000 : ℚ) : ℝ) ≤ stT128 61 := by
  have hc : ((125627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10053049421/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((125627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c62 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((721677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1911437/10000000) (δ := 3299/500000000) (ψ := -8717/31250) 128 84
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t62 : ((916467011627/10000000000000 : ℚ) : ℝ) ≤ stT128 62 := by
  have hc : ((721627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((916467011627/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((721627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c63 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-946377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1406313/2000000) (δ := 3299/500000000) (ψ := -8717/31250) 128 84
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t63 : ((-596193170807/5000000000000 : ℚ) : ℝ) ≤ stT128 63 := by
  have hc : ((-946427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-596193170807/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-946427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c64 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((115759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1818471/5000000) (δ := 6491/1000000000) (ψ := -8717/31250) 128 85
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t64 : ((115709/8000000 : ℚ) : ℝ) ≤ stT128 64 := by
  have hc : ((115709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115709/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((115709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c65 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((53933/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 662201/5000000) (δ := 6491/1000000000) (ψ := -8717/31250) 128 85
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t65 : ((535134069333/5000000000000 : ℚ) : ℝ) ≤ stT128 65 := by
  have hc : ((431439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((535134069333/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((431439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c66 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-395733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3105001/5000000) (δ := 6491/1000000000) (ψ := -8717/31250) 128 85
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t66 : ((-48714445857/500000000000 : ℚ) : ℝ) ≤ stT128 66 := by
  have hc : ((-197879/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48714445857/500000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-197879/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c67 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-298897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4685833/10000000) (δ := 6419/1000000000) (ψ := -8717/31250) 128 86
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t67 : ((-73044411033/2000000000000 : ℚ) : ℝ) ≤ stT128 67 := by
  have hc : ((-298947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73044411033/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-298947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c68 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((499879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 54999/10000000) (δ := 6419/1000000000) (ψ := -8717/31250) 128 86
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t68 : ((151540487253/1250000000000 : ℚ) : ℝ) ≤ stT128 68 := by
  have hc : ((249927/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151540487253/1250000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((249927/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c69 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-39303/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 945323/2000000) (δ := 6419/1000000000) (ψ := -8717/31250) 128 86
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t69 : ((-189291177583/5000000000000 : ℚ) : ℝ) ≤ stT128 69 := by
  have hc : ((-157237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-189291177583/5000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-157237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c70 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-830491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1594241/2500000) (δ := 3263/500000000) (ψ := -8717/31250) 128 87
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t70 : ((-992686688889/10000000000000 : ℚ) : ℝ) ≤ stT128 70 := by
  have hc : ((-830541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-992686688889/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-830541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c71 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((370863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -459473/2500000) (δ := 3263/500000000) (ψ := -8717/31250) 128 87
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t71 : ((220051746239/2500000000000 : ℚ) : ℝ) ≤ stT128 71 := by
  have hc : ((185419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220051746239/2500000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((185419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c72 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((9863/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 659431/2500000) (δ := 3263/500000000) (ψ := -8717/31250) 128 87
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t72 : ((5811237741/100000000000 : ℚ) : ℝ) ≤ stT128 72 := by
  have hc : ((4931/10000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5811237741/100000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((4931/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c73 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-948933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 352579/500000) (δ := 3263/500000000) (ψ := -8717/31250) 128 87
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t73 : ((-277675272749/2500000000000 : ℚ) : ℝ) ≤ stT128 73 := by
  have hc : ((-948983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277675272749/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-948983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c74 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-37419/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33614/78125) (δ := 657/100000000) (ψ := -8717/31250) 128 88
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t74 : ((-87026515651/5000000000000 : ℚ) : ℝ) ≤ stT128 74 := by
  have hc : ((-74863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87026515651/5000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-74863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c75 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((249999/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9/12500) (δ := 657/100000000) (ψ := -8717/31250) 128 88
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t75 : ((5773188231/50000000000 : ℚ) : ℝ) ≤ stT128 75 := by
  have hc : ((499973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5773188231/50000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((499973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c76 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-121409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 132227/312500) (δ := 657/100000000) (ψ := -8717/31250) 128 88
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t76 : ((-139323068261/10000000000000 : ℚ) : ℝ) ≤ stT128 76 := by
  have hc : ((-121459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139323068261/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-121459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c77 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-194997/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7293627/10000000) (δ := 6463/1000000000) (ψ := -8717/31250) 128 89
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t77 : ((-111115573621/1000000000000 : ℚ) : ℝ) ≤ stT128 77 := by
  have hc : ((-195007/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111115573621/1000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-195007/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c78 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((12011/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3164539/10000000) (δ := 6463/1000000000) (ψ := -8717/31250) 128 89
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t78 : ((13597514493/400000000000 : ℚ) : ℝ) ≤ stT128 78 := by
  have hc : ((12009/40000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13597514493/400000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((12009/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c79 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((233551/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 911941/10000000) (δ := 6463/1000000000) (ψ := -8717/31250) 128 89
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t79 : ((525502260699/5000000000000 : ℚ) : ℝ) ≤ stT128 79 := by
  have hc : ((467077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((525502260699/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((467077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c80 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-393161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4937157/10000000) (δ := 6463/1000000000) (ψ := -8717/31250) 128 89
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t80 : ((-219811633587/5000000000000 : ℚ) : ℝ) ≤ stT128 80 := by
  have hc : ((-393211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219811633587/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-393211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c81 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-455859/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3397803/5000000) (δ := 403/62500000) (ψ := -8717/31250) 128 90
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t81 : ((-15829318219/156250000000 : ℚ) : ℝ) ≤ stT128 81 := by
  have hc : ((-113971/125000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15829318219/156250000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-113971/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c82 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((410613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1434587/5000000) (δ := 403/62500000) (ψ := -8717/31250) 128 90
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t82 : ((90678175869/2000000000000 : ℚ) : ℝ) ≤ stT128 82 := by
  have hc : ((410563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90678175869/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((410563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c83 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((919547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 504837/5000000) (δ := 403/62500000) (ψ := -8717/31250) 128 90
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t83 : ((504639263037/5000000000000 : ℚ) : ℝ) ≤ stT128 83 := by
  have hc : ((919497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((504639263037/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((919497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c84 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-178951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2421021/5000000) (δ := 803/62500000) (ψ := -8717/31250) 128 90
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t84 : ((-610246637/15625000000 : ℚ) : ℝ) ≤ stT128 84 := by
  have hc : ((-5593/15625 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-610246637/15625000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-5593/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c85 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-952323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7078897/10000000) (δ := 1311/200000000) (ψ := -8717/31250) 128 91
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t85 : ((-1032994231569/10000000000000 : ℚ) : ℝ) ≤ stT128 85 := by
  have hc : ((-952373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1032994231569/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-952373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c86 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((58533/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3336177/10000000) (δ := 1311/200000000) (ψ := -8717/31250) 128 91
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t86 : ((126208470407/5000000000000 : ℚ) : ℝ) ≤ stT128 86 := by
  have hc : ((117041/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126208470407/5000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((117041/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c87 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((989459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 363311/10000000) (δ := 1311/200000000) (ψ := -8717/31250) 128 91
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t87 : ((66297328863/625000000000 : ℚ) : ℝ) ≤ stT128 87 := by
  have hc : ((989409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66297328863/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((989409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c88 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-37393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 804099/2000000) (δ := 1311/200000000) (ψ := -8717/31250) 128 91
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t88 : ((-9978596943/2500000000000 : ℚ) : ℝ) ≤ stT128 88 := by
  have hc : ((-37443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9978596943/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-37443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c89 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-996213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1527267/2000000) (δ := 1311/200000000) (ψ := -8717/31250) 128 91
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t89 : ((-528018393737/5000000000000 : ℚ) : ℝ) ≤ stT128 89 := by
  have hc : ((-996263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-528018393737/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-996263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c90 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-225711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4496173/10000000) (δ := 6541/1000000000) (ψ := -8717/31250) 128 92
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t90 : ((-237973089773/10000000000000 : ℚ) : ℝ) ≤ stT128 90 := by
  have hc : ((-225761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237973089773/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-225761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c91 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((46357/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -960221/10000000) (δ := 12941/1000000000) (ψ := -8717/31250) 128 92
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t91 : ((24296340339/250000000000 : ℚ) : ℝ) ≤ stT128 91 := by
  have hc : ((92709/100000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24296340339/250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((92709/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c92 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((131941/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 101483/400000) (δ := 6541/1000000000) (ψ := -8717/31250) 128 92
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t92 : ((68772480051/1250000000000 : ℚ) : ℝ) ≤ stT128 92 := by
  have hc : ((263857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68772480051/1250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((263857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c93 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-46029/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5996563/10000000) (δ := 6541/1000000000) (ψ := -8717/31250) 128 92
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t93 : ((-47733104083/625000000000 : ℚ) : ℝ) ≤ stT128 93 := by
  have hc : ((-368257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47733104083/625000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-368257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c94 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-810359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -786113/1250000) (δ := 3217/500000000) (ψ := -8717/31250) 128 93
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t94 : ((-417936835799/5000000000000 : ℚ) : ℝ) ≤ stT128 94 := by
  have hc : ((-810409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-417936835799/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-810409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c95 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((199187/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -362829/1250000) (δ := 3217/500000000) (ψ := -8717/31250) 128 93
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t95 : ((51083957609/1250000000000 : ℚ) : ℝ) ≤ stT128 95 := by
  have hc : ((99581/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51083957609/1250000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((99581/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c96 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((983973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56023/1250000) (δ := 3217/500000000) (ψ := -8717/31250) 128 93
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t96 : ((50210574613/500000000000 : ℚ) : ℝ) ≤ stT128 96 := by
  have hc : ((983923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50210574613/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((983923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c97 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((32519/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94107/250000) (δ := 3217/500000000) (ψ := -8717/31250) 128 93
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t97 : ((8248163231/1250000000000 : ℚ) : ℝ) ≤ stT128 97 := by
  have hc : ((16247/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8248163231/1250000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((16247/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c98 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-59267/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 176159/250000) (δ := 3217/500000000) (ψ := -8717/31250) 128 93
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t98 : ((-478975156633/5000000000000 : ℚ) : ℝ) ≤ stT128 98 := by
  have hc : ((-474161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-478975156633/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-474161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c99 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-13999/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1082567/2000000) (δ := 1619/250000000) (ψ := -8717/31250) 128 94
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t99 : ((-28141566519/500000000000 : ℚ) : ℝ) ≤ stT128 99 := by
  have hc : ((-56001/100000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28141566519/500000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-56001/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c100 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((159539/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2196739/10000000) (δ := 1619/250000000) (ψ := -8717/31250) 128 94
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t100 : ((319052680947/5000000000000 : ℚ) : ℝ) ≤ stT128 100 := by
  have hc : ((319053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((319052680947/5000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((319053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c101 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((461507/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 987389/10000000) (δ := 1619/250000000) (ψ := -8717/31250) 128 94
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t101 : ((229595832417/2500000000000 : ℚ) : ℝ) ≤ stT128 101 := by
  have hc : ((230741/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229595832417/2500000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((230741/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c102 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-1703/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33121/80000) (δ := 1619/250000000) (ψ := -8717/31250) 128 94
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t102 : ((-52725381/6250000000 : ℚ) : ℝ) ≤ stT128 102 := by
  have hc : ((-213/2500 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52725381/6250000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-213/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c103 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-972103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7262077/10000000) (δ := 1619/250000000) (ψ := -8717/31250) 128 94
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t103 : ((-95789151549/1000000000000 : ℚ) : ℝ) ≤ stT128 103 := by
  have hc : ((-972153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95789151549/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-972153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c104 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-108067/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2677039/5000000) (δ := 823/125000000) (ψ := -8717/31250) 128 95
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t104 : ((-105978252737/2000000000000 : ℚ) : ℝ) ≤ stT128 104 := by
  have hc : ((-108077/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105978252737/2000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-108077/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c105 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((304207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1145919/5000000) (δ := 823/125000000) (ψ := -8717/31250) 128 95
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t105 : ((1484256069/25000000000 : ℚ) : ℝ) ≤ stT128 105 := by
  have hc : ((152091/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1484256069/25000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((152091/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c106 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((478177/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 370673/5000000) (δ := 823/125000000) (ψ := -8717/31250) 128 95
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t106 : ((11610546633/125000000000 : ℚ) : ℝ) ≤ stT128 106 := by
  have hc : ((59769/62500 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11610546633/125000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((59769/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c107 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((723/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1873041/5000000) (δ := 823/125000000) (ψ := -8717/31250) 128 95
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t107 : ((17461669/2500000000 : ℚ) : ℝ) ≤ stT128 107 := by
  have hc : ((289/4000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17461669/2500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((289/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c108 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-449689/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 134457/200000) (δ := 823/125000000) (ψ := -8717/31250) 128 95
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t108 : ((-216368873107/2500000000000 : ℚ) : ℝ) ≤ stT128 108 := by
  have hc : ((-224857/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-216368873107/2500000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-224857/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c109 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-746991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3017901/5000000) (δ := 407/62500000) (ψ := -8717/31250) 128 96
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t109 : ((-715536039907/10000000000000 : ℚ) : ℝ) ≤ stT128 109 := by
  have hc : ((-747041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-715536039907/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-747041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c110 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((319721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1556701/5000000) (δ := 407/62500000) (ψ := -8717/31250) 128 96
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t110 : ((152397075501/5000000000000 : ℚ) : ℝ) ≤ stT128 110 := by
  have hc : ((319671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152397075501/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((319671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c111 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((49811/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -108717/5000000) (δ := 407/62500000) (ψ := -8717/31250) 128 96
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t111 : ((94552172869/1000000000000 : ℚ) : ℝ) ≤ stT128 111 := by
  have hc : ((99617/100000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94552172869/1000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((99617/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c112 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((487993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1326259/5000000) (δ := 407/62500000) (ψ := -8717/31250) 128 96
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t112 : ((461062708073/10000000000000 : ℚ) : ℝ) ≤ stT128 112 := by
  have hc : ((487943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((461062708073/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((487943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c113 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-58753/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2748499/5000000) (δ := 407/62500000) (ψ := -8717/31250) 128 96
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t113 : ((-27637442259/500000000000 : ℚ) : ℝ) ≤ stT128 113 := by
  have hc : ((-29379/50000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27637442259/500000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-29379/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c114 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-982943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7391573/10000000) (δ := 1281/200000000) (ψ := -8717/31250) 128 97
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t114 : ((-460328740949/5000000000000 : ℚ) : ℝ) ≤ stT128 114 := by
  have hc : ((-982993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-460328740949/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-982993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c115 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-132363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4596789/10000000) (δ := 1281/200000000) (ψ := -8717/31250) 128 97
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t115 : ((-6172623597/250000000000 : ℚ) : ℝ) ≤ stT128 115 := by
  have hc : ((-33097/125000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6172623597/250000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-33097/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c116 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((372423/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1826229/10000000) (δ := 1281/200000000) (ψ := -8717/31250) 128 97
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t116 : ((43220325681/625000000000 : ℚ) : ℝ) ≤ stT128 116 := by
  have hc : ((186199/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43220325681/625000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((186199/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c117 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((233241/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 920587/10000000) (δ := 1281/200000000) (ψ := -8717/31250) 128 97
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t117 : ((862478993/10000000000 : ℚ) : ℝ) ≤ stT128 117 := by
  have hc : ((466457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((862478993/10000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((466457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c118 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((2259/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3644011/10000000) (δ := 1281/200000000) (ψ := -8717/31250) 128 97
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t118 : ((519664023/50000000000 : ℚ) : ℝ) ≤ stT128 118 := by
  have hc : ((1129/10000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((519664023/50000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((1129/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c119 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-205793/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6344427/10000000) (δ := 1281/200000000) (ψ := -8717/31250) 128 97
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t119 : ((-377323392089/5000000000000 : ℚ) : ℝ) ≤ stT128 119 := by
  have hc : ((-411611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-377323392089/5000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-411611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c120 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-892779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83571/125000) (δ := 1301/200000000) (ψ := -8717/31250) 128 98
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t120 : ((-815037702059/10000000000000 : ℚ) : ℝ) ≤ stT128 120 := by
  have hc : ((-892829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-815037702059/10000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-892829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c121 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-20609/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -251879/625000) (δ := 1301/200000000) (ψ := -8717/31250) 128 98
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t121 : ((-9379091847/2500000000000 : ℚ) : ℝ) ≤ stT128 121 := by
  have hc : ((-10317/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9379091847/2500000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-10317/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c122 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((848039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87269/625000) (δ := 1301/200000000) (ψ := -8717/31250) 128 98
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t122 : ((767732777073/10000000000000 : ℚ) : ℝ) ≤ stT128 122 := by
  have hc : ((847989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((767732777073/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((847989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c123 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((88403/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75997/625000) (δ := 1301/200000000) (ψ := -8717/31250) 128 98
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t123 : ((39852868131/500000000000 : ℚ) : ℝ) ≤ stT128 123 := by
  have hc : ((44199/50000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39852868131/500000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((44199/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c124 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((11989/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 237941/625000) (δ := 1301/200000000) (ψ := -8717/31250) 128 98
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t124 : ((10755208389/2500000000000 : ℚ) : ℝ) ≤ stT128 124 := by
  have hc : ((23953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10755208389/2500000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((23953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c125 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-41529/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 79717/125000) (δ := 1301/200000000) (ψ := -8717/31250) 128 98
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t125 : ((-18573468241/250000000000 : ℚ) : ℝ) ≤ stT128 125 := by
  have hc : ((-83063/100000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18573468241/250000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-83063/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c126 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-181853/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -339039/500000) (δ := 6591/1000000000) (ψ := -8717/31250) 128 99
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t126 : ((-162016472673/2000000000000 : ℚ) : ℝ) ≤ stT128 126 := by
  have hc : ((-181863/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162016472673/2000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-181863/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c127 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-1293/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1062787/2500000) (δ := 6591/1000000000) (ψ := -8717/31250) 128 99
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t127 : ((-2295592559/200000000000 : ℚ) : ℝ) ≤ stT128 127 := by
  have hc : ((-2587/20000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2295592559/200000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-2587/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c128 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((767073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -435331/2500000) (δ := 6591/1000000000) (ψ := -8717/31250) 128 99
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t128 : ((677958590309/10000000000000 : ℚ) : ℝ) ≤ stT128 128 := by
  have hc : ((767023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((677958590309/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((767023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c129 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((955457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 37449/500000) (δ := 6591/1000000000) (ψ := -8717/31250) 128 99
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t129 : ((16823761863/200000000000 : ℚ) : ℝ) ≤ stT128 129 := by
  have hc : ((955407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16823761863/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((955407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c130 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((139517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 161001/500000) (δ := 6591/1000000000) (ψ := -8717/31250) 128 99
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t130 : ((15292821817/625000000000 : ℚ) : ℝ) ≤ stT128 130 := by
  have hc : ((34873/125000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15292821817/625000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((34873/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c131 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-128547/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1418037/2500000) (δ := 6591/1000000000) (ψ := -8717/31250) 128 99
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t131 : ((-22464178737/400000000000 : ℚ) : ℝ) ≤ stT128 131 := by
  have hc : ((-128557/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22464178737/400000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-128557/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c132 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-994939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7602343/10000000) (δ := 1621/250000000) (ψ := -8717/31250) 128 100
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t132 : ((-866027480721/10000000000000 : ℚ) : ℝ) ≤ stT128 132 := by
  have hc : ((-994989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-866027480721/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-994989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c133 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-483019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5187239/10000000) (δ := 1621/250000000) (ψ := -8717/31250) 128 100
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t133 : ((-41887396059/1000000000000 : ℚ) : ℝ) ≤ stT128 133 := by
  have hc : ((-483069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41887396059/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-483069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c134 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((109799/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2790231/10000000) (δ := 3221/250000000) (ψ := -8717/31250) 128 100
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t134 : ((47420522091/1250000000000 : ℚ) : ℝ) ≤ stT128 134 := by
  have hc : ((219573/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47420522091/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((219573/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c135 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((493257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -411047/10000000) (δ := 1621/250000000) (ψ := -8717/31250) 128 100
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t135 : ((13265813737/156250000000 : ℚ) : ℝ) ≤ stT128 135 := by
  have hc : ((30827/31250 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13265813737/156250000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((30827/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c136 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((710749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 390117/2000000) (δ := 1621/250000000) (ψ := -8717/31250) 128 100
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t136 : ((152354676727/2500000000000 : ℚ) : ℝ) ≤ stT128 136 := by
  have hc : ((710699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152354676727/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((710699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c137 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-18331/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4294937/10000000) (δ := 1621/250000000) (ψ := -8717/31250) 128 100
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t137 : ((-31333152471/2500000000000 : ℚ) : ℝ) ≤ stT128 137 := by
  have hc : ((-73349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31333152471/2500000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-73349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c138 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-881053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6622201/10000000) (δ := 1621/250000000) (ψ := -8717/31250) 128 100
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t138 : ((-750045096471/10000000000000 : ℚ) : ℝ) ≤ stT128 138 := by
  have hc : ((-881103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-750045096471/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-881103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c139 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-181669/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3387633/5000000) (δ := 6427/1000000000) (ψ := -8717/31250) 128 101
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t139 : ((-154098129331/2000000000000 : ℚ) : ℝ) ≤ stT128 139 := by
  have hc : ((-181679/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154098129331/2000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-181679/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c140 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-219929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2240673/5000000) (δ := 6427/1000000000) (ψ := -8717/31250) 128 101
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t140 : ((-37183270349/2000000000000 : ℚ) : ℝ) ≤ stT128 140 := by
  have hc : ((-219979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37183270349/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-219979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c141 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((317993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1101889/5000000) (δ := 6427/1000000000) (ψ := -8717/31250) 128 101
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t141 : ((16736066823/312500000000 : ℚ) : ℝ) ≤ stT128 141 := by
  have hc : ((19873/31250 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16736066823/312500000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((19873/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c142 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((999733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 28863/5000000) (δ := 6427/1000000000) (ψ := -8717/31250) 128 101
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t142 : ((838914979623/10000000000000 : ℚ) : ℝ) ≤ stT128 142 := by
  have hc : ((999683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((838914979623/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((999683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c143 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((604751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1151679/5000000) (δ := 6427/1000000000) (ψ := -8717/31250) 128 101
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t143 : ((252838186821/5000000000000 : ℚ) : ℝ) ≤ stT128 143 := by
  have hc : ((604701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252838186821/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((604701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c144 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-240157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 453331/1000000) (δ := 6427/1000000000) (ψ := -8717/31250) 128 101
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t144 : ((-100086330069/5000000000000 : ℚ) : ℝ) ≤ stT128 144 := by
  have hc : ((-240207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100086330069/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-240207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c145 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-225927/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 674787/1000000) (δ := 6427/1000000000) (ψ := -8717/31250) 128 101
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t145 : ((-75053034989/1000000000000 : ℚ) : ℝ) ≤ stT128 145 := by
  have hc : ((-451879/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75053034989/1000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-451879/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c146 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-56619/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1352153/2000000) (δ := 3267/500000000) (ψ := -8717/31250) 128 102
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t146 : ((-187443241531/2500000000000 : ℚ) : ℝ) ≤ stT128 146 := by
  have hc : ((-452977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187443241531/2500000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-452977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c147 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-128441/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4576477/10000000) (δ := 3267/500000000) (ψ := -8717/31250) 128 102
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t147 : ((-52978543371/2500000000000 : ℚ) : ℝ) ≤ stT128 147 := by
  have hc : ((-64233/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52978543371/2500000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-64233/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c148 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((571233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2406973/10000000) (δ := 3267/500000000) (ψ := -8717/31250) 128 102
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t148 : ((234754499451/5000000000000 : ℚ) : ℝ) ≤ stT128 148 := by
  have hc : ((571183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234754499451/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((571183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c149 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((497461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -252061/10000000) (δ := 3267/500000000) (ψ := -8717/31250) 128 102
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t149 : ((101878747929/1250000000000 : ℚ) : ℝ) ≤ stT128 149 := by
  have hc : ((124359/125000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101878747929/1250000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((124359/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c150 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((182007/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1888387/10000000) (δ := 3267/500000000) (ψ := -8717/31250) 128 102
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t150 : ((18574722659/312500000000 : ℚ) : ℝ) ≤ stT128 150 := by
  have hc : ((363989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18574722659/312500000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((363989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c151 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-1753/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4014659/10000000) (δ := 3267/500000000) (ψ := -8717/31250) 128 102
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t151 : ((-2857213179/1000000000000 : ℚ) : ℝ) ≤ stT128 151 := by
  have hc : ((-3511/100000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2857213179/1000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-3511/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c152 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-770711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6126883/10000000) (δ := 3267/500000000) (ψ := -8717/31250) 128 102
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t152 : ((-156292603297/2500000000000 : ℚ) : ℝ) ≤ stT128 152 := by
  have hc : ((-770761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156292603297/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-770761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c153 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-988993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7482713/10000000) (δ := 3281/500000000) (ψ := -8717/31250) 128 103
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t153 : ((-799594780479/10000000000000 : ℚ) : ℝ) ≤ stT128 153 := by
  have hc : ((-989043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-799594780479/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-989043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c154 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-555037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5398009/10000000) (δ := 3281/500000000) (ψ := -8717/31250) 128 103
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t154 : ((-447301871601/10000000000000 : ℚ) : ℝ) ≤ stT128 154 := by
  have hc : ((-555087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-447301871601/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-555087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c155 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((237773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3326809/10000000) (δ := 3281/500000000) (ψ := -8717/31250) 128 103
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t155 : ((190943630337/10000000000000 : ℚ) : ℝ) ≤ stT128 155 := by
  have hc : ((237723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190943630337/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((237723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c156 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((873929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1268921/10000000) (δ := 3281/500000000) (ψ := -8717/31250) 128 103
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t156 : ((1093222629/15625000000 : ℚ) : ℝ) ≤ stT128 156 := by
  have hc : ((873879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1093222629/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((873879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c157 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((476117/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 155163/2000000) (δ := 3281/500000000) (ψ := -8717/31250) 128 103
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t157 : ((47495294989/625000000000 : ℚ) : ℝ) ≤ stT128 157 := by
  have hc : ((119023/125000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47495294989/625000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((119023/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c158 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((432959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2807559/10000000) (δ := 3281/500000000) (ψ := -8717/31250) 128 103
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t158 : ((344403785313/10000000000000 : ℚ) : ℝ) ≤ stT128 158 := by
  have hc : ((432909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((344403785313/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((432909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c159 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-88023/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4826503/10000000) (δ := 3281/500000000) (ψ := -8717/31250) 128 103
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t159 : ((-34908364673/1250000000000 : ℚ) : ℝ) ≤ stT128 159 := by
  have hc : ((-176071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34908364673/1250000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-176071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c160 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-36709/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 273311/400000) (δ := 3281/500000000) (ψ := -8717/31250) 128 103
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t160 : ((-2902261527/40000000000 : ℚ) : ℝ) ≤ stT128 160 := by
  have hc : ((-36711/40000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2902261527/40000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-36711/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c161 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-925281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1720357/2500000) (δ := 1291/200000000) (ψ := -8717/31250) 128 104
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t161 : ((-729263539741/10000000000000 : ℚ) : ℝ) ≤ stT128 161 := by
  have hc : ((-925331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-729263539741/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-925331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c162 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-379447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1224997/2500000) (δ := 1291/200000000) (ψ := -8717/31250) 128 104
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t162 : ((-11926452219/400000000000 : ℚ) : ℝ) ≤ stT128 162 := by
  have hc : ((-379497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11926452219/400000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-379497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c163 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((388037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -146537/500000) (δ := 1291/200000000) (ψ := -8717/31250) 128 104
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t163 : ((15194734881/500000000000 : ℚ) : ℝ) ≤ stT128 163 := by
  have hc : ((387987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15194734881/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((387987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c164 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((925129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -243389/2500000) (δ := 1291/200000000) (ψ := -8717/31250) 128 104
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t164 : ((180591147143/2500000000000 : ℚ) : ℝ) ≤ stT128 164 := by
  have hc : ((925079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180591147143/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((925079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c165 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((462703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 242931/2500000) (δ := 1291/200000000) (ψ := -8717/31250) 128 104
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t165 : ((90048474411/1250000000000 : ℚ) : ℝ) ≤ stT128 165 := by
  have hc : ((231339/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90048474411/1250000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((231339/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c166 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((39741/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 145263/500000) (δ := 1291/200000000) (ψ := -8717/31250) 128 104
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t166 : ((77102741/2500000000 : ℚ) : ℝ) ≤ stT128 166 := by
  have hc : ((4967/12500 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77102741/2500000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((4967/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c167 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-352357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1206803/2500000) (δ := 1291/200000000) (ψ := -8717/31250) 128 104
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t167 : ((-4260953037/156250000000 : ℚ) : ℝ) ≤ stT128 167 := by
  have hc : ((-352407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4260953037/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-352407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c168 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-901949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1684411/2500000) (δ := 1291/200000000) (ψ := -8717/31250) 128 104
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t168 : ((-695907562483/10000000000000 : ℚ) : ℝ) ≤ stT128 168 := by
  have hc : ((-901999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-695907562483/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-901999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c169 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-951377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7071183/10000000) (δ := 1291/200000000) (ψ := -8717/31250) 128 105
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t169 : ((-731867142637/10000000000000 : ℚ) : ℝ) ≤ stT128 169 := by
  have hc : ((-951427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-731867142637/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-951427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c170 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-481631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5183279/10000000) (δ := 1291/200000000) (ψ := -8717/31250) 128 105
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t170 : ((-73886493633/2000000000000 : ℚ) : ℝ) ≤ stT128 170 := by
  have hc : ((-481681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73886493633/2000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-481681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c171 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((245677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3306447/10000000) (δ := 1291/200000000) (ψ := -8717/31250) 128 105
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t171 : ((187835633813/10000000000000 : ℚ) : ℝ) ≤ stT128 171 := by
  have hc : ((245627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187835633813/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((245627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c172 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((419263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1440559/10000000) (δ := 1291/200000000) (ψ := -8717/31250) 128 105
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t172 : ((39958202637/625000000000 : ℚ) : ℝ) ≤ stT128 172 := by
  have hc : ((209619/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39958202637/625000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((209619/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c173 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((493143/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 414513/10000000) (δ := 1291/200000000) (ψ := -8717/31250) 128 105
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t173 : ((37491021863/500000000000 : ℚ) : ℝ) ≤ stT128 173 := by
  have hc : ((246559/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37491021863/500000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((246559/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c174 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((309409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2258897/10000000) (δ := 1291/200000000) (ψ := -8717/31250) 128 105
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t174 : ((14658961977/312500000000 : ℚ) : ℝ) ≤ stT128 174 := by
  have hc : ((38673/62500 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14658961977/312500000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((38673/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c175 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-16561/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4092721/10000000) (δ := 1291/200000000) (ψ := -8717/31250) 128 105
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t175 : ((-25056778563/5000000000000 : ℚ) : ℝ) ≤ stT128 175 := by
  have hc : ((-33147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25056778563/5000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-33147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c176 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-714309/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5916081/10000000) (δ := 1291/200000000) (ψ := -8717/31250) 128 105
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t176 : ((-538468812661/10000000000000 : ℚ) : ℝ) ≤ stT128 176 := by
  have hc : ((-714359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-538468812661/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-714359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c177 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-998753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7729137/10000000) (δ := 1291/200000000) (ψ := -8717/31250) 128 105
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t177 : ((-750747278541/10000000000000 : ℚ) : ℝ) ≤ stT128 177 := by
  have hc : ((-998803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-750747278541/10000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-998803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c178 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-783083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -617601/1000000) (δ := 6563/1000000000) (ψ := -8717/31250) 128 106
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t178 : ((-146745810939/2500000000000 : ℚ) : ℝ) ≤ stT128 178 := by
  have hc : ((-783133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146745810939/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-783133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c179 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-90751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2191637/5000000) (δ := 6563/1000000000) (ψ := -8717/31250) 128 106
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t179 : ((-2120289073/156250000000 : ℚ) : ℝ) ≤ stT128 179 := by
  have hc : ((-11347/62500 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2120289073/156250000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-11347/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c180 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((506029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1300277/5000000) (δ := 6563/1000000000) (ψ := -8717/31250) 128 106
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t180 : ((75426795509/2000000000000 : ℚ) : ℝ) ≤ stT128 180 := by
  have hc : ((505979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75426795509/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((505979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c181 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((945693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -82769/1000000) (δ := 6563/1000000000) (ψ := -8717/31250) 128 106
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t181 : ((351445384021/5000000000000 : ℚ) : ℝ) ≤ stT128 181 := by
  have hc : ((945643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((351445384021/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((945643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c182 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((465409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 467691/5000000) (δ := 6563/1000000000) (ψ := -8717/31250) 128 106
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t182 : ((43120678077/625000000000 : ℚ) : ℝ) ≤ stT128 182 := by
  have hc : ((58173/62500 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43120678077/625000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((58173/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c183 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((475267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1344411/5000000) (δ := 6563/1000000000) (ψ := -8717/31250) 128 106
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t183 : ((351290385957/10000000000000 : ℚ) : ℝ) ≤ stT128 183 := by
  have hc : ((475217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((351290385957/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((475217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c184 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-40181/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2216347/5000000) (δ := 6563/1000000000) (ψ := -8717/31250) 128 106
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t184 : ((-2962920711/200000000000 : ℚ) : ℝ) ≤ stT128 184 := by
  have hc : ((-40191/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2962920711/200000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-40191/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c185 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-195217/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3083563/5000000) (δ := 6563/1000000000) (ψ := -8717/31250) 128 106
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t185 : ((-57414262737/1000000000000 : ℚ) : ℝ) ≤ stT128 185 := by
  have hc : ((-390459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57414262737/1000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-390459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c186 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-999883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3907891/5000000) (δ := 6533/1000000000) (ψ := -8717/31250) 128 107
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t186 : ((-183296718297/2500000000000 : ℚ) : ℝ) ≤ stT128 186 := by
  have hc : ((-999933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183296718297/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-999933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c187 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-3819/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3049971/5000000) (δ := 6533/1000000000) (ψ := -8717/31250) 128 107
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t187 : ((-11171657621/200000000000 : ℚ) : ℝ) ≤ stT128 187 := by
  have hc : ((-15277/20000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11171657621/200000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-15277/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c188 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-92719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2196643/5000000) (δ := 6533/1000000000) (ψ := -8717/31250) 128 107
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t188 : ((-338202589/25000000000 : ℚ) : ℝ) ≤ stT128 188 := by
  have hc : ((-11593/62500 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-338202589/25000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-11593/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c189 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((472861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1347827/5000000) (δ := 6533/1000000000) (ψ := -8717/31250) 128 107
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t189 : ((10747466841/312500000000 : ℚ) : ℝ) ≤ stT128 189 := by
  have hc : ((472811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10747466841/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((472811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c190 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((183993/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -503507/5000000) (δ := 6533/1000000000) (ψ := -8717/31250) 128 107
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t190 : ((33368812727/500000000000 : ℚ) : ℝ) ≤ stT128 190 := by
  have hc : ((183983/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33368812727/500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((183983/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c191 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((482003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 336397/5000000) (δ := 6533/1000000000) (ψ := -8717/31250) 128 107
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t191 : ((87186687343/1250000000000 : ℚ) : ℝ) ≤ stT128 191 := by
  have hc : ((240989/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87186687343/1250000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((240989/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c192 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((147947/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1171901/5000000) (δ := 6533/1000000000) (ψ := -8717/31250) 128 107
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t192 : ((213524811003/5000000000000 : ℚ) : ℝ) ≤ stT128 192 := by
  have hc : ((295869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213524811003/5000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((295869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c193 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-15827/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2003069/5000000) (δ := 6533/1000000000) (ψ := -8717/31250) 128 107
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t193 : ((-356578851/156250000000 : ℚ) : ℝ) ≤ stT128 193 := by
  have hc : ((-3963/125000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-356578851/156250000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-3963/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c194 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-638973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2829949/5000000) (δ := 6533/1000000000) (ψ := -8717/31250) 128 107
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t194 : ((-458792314057/10000000000000 : ℚ) : ℝ) ≤ stT128 194 := by
  have hc : ((-639023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-458792314057/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-639023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c195 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-975999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3652573/5000000) (δ := 6533/1000000000) (ψ := -8717/31250) 128 107
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t195 : ((-139792665927/2000000000000 : ℚ) : ℝ) ≤ stT128 195 := by
  have hc : ((-976049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139792665927/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-976049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c196 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-453393/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1353197/2000000) (δ := 3213/500000000) (ψ := -8717/31250) 128 108
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t196 : ((-80967532387/1250000000000 : ℚ) : ℝ) ≤ stT128 196 := by
  have hc : ((-226709/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80967532387/1250000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-226709/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c197 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-232747/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5137473/10000000) (δ := 3213/500000000) (ψ := -8717/31250) 128 108
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t197 : ((-41460824903/1250000000000 : ℚ) : ℝ) ≤ stT128 197 := by
  have hc : ((-58193/125000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41460824903/1250000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-58193/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c198 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((163177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3517217/10000000) (δ := 3213/500000000) (ψ := -8717/31250) 128 108
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t198 : ((115929301963/10000000000000 : ℚ) : ℝ) ≤ stT128 198 := by
  have hc : ((163127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115929301963/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((163127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c199 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((723423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1905121/10000000) (δ := 3213/500000000) (ψ := -8717/31250) 128 108
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t199 : ((512785375613/10000000000000 : ℚ) : ℝ) ≤ stT128 199 := by
  have hc : ((723373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((512785375613/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((723373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c200 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((198551/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -301121/10000000) (δ := 3213/500000000) (ψ := -8717/31250) 128 108
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t200 : ((70194766173/1000000000000 : ℚ) : ℝ) ≤ stT128 200 := by
  have hc : ((198541/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70194766173/1000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((198541/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c201 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((868829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1294911/10000000) (δ := 3213/500000000) (ψ := -8717/31250) 128 108
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t201 : ((122557784751/2000000000000 : ℚ) : ℝ) ≤ stT128 201 := by
  have hc : ((868779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122557784751/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((868779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c202 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((202787/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 115319/400000) (δ := 3213/500000000) (ψ := -8717/31250) 128 108
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t202 : ((71331367457/2500000000000 : ℚ) : ℝ) ≤ stT128 202 := by
  have hc : ((101381/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71331367457/2500000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((101381/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c203 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-42571/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4463231/10000000) (δ := 3213/500000000) (ψ := -8717/31250) 128 108
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t203 : ((-29886028403/2000000000000 : ℚ) : ℝ) ≤ stT128 203 := by
  have hc : ((-42581/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29886028403/2000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-42581/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c204 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-746967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6035711/10000000) (δ := 3213/500000000) (ψ := -8717/31250) 128 108
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t204 : ((-523017229397/10000000000000 : ℚ) : ℝ) ≤ stT128 204 := by
  have hc : ((-747017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-523017229397/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-747017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c205 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-198973/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7600511/10000000) (δ := 3213/500000000) (ψ := -8717/31250) 128 108
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t205 : ((-138975895673/2000000000000 : ℚ) : ℝ) ≤ stT128 205 := by
  have hc : ((-198983/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138975895673/2000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-198983/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c206 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-21677/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1637567/2500000) (δ := 1621/250000000) (ψ := -8717/31250) 128 109
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t206 : ((-30207947671/500000000000 : ℚ) : ℝ) ≤ stT128 206 := by
  have hc : ((-86713/100000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30207947671/500000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-86713/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c207 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-208189/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1250159/2500000) (δ := 1621/250000000) (ψ := -8717/31250) 128 109
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t207 : ((-72359466243/2500000000000 : ℚ) : ℝ) ≤ stT128 207 := by
  have hc : ((-104107/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72359466243/2500000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-104107/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c208 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((186317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -172923/500000) (δ := 1621/250000000) (ψ := -8717/31250) 128 109
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t208 : ((1033223049/80000000000 : ℚ) : ℝ) ≤ stT128 208 := by
  have hc : ((186267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1033223049/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((186267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c209 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((718279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -480919/2500000) (δ := 1621/250000000) (ψ := -8717/31250) 128 109
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t209 : ((248404527253/5000000000000 : ℚ) : ℝ) ≤ stT128 209 := by
  have hc : ((718229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((248404527253/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((718229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c210 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((987467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19811/500000) (δ := 1621/250000000) (ψ := -8717/31250) 128 109
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t210 : ((136276382421/2000000000000 : ℚ) : ℝ) ≤ stT128 210 := by
  have hc : ((987417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136276382421/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((987417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c211 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((450313/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 280993/2500000) (δ := 1621/250000000) (ψ := -8717/31250) 128 109
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t211 : ((4843607301/78125000000 : ℚ) : ℝ) ≤ stT128 211 := by
  have hc : ((28143/31250 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4843607301/78125000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((28143/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c212 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((246707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 659241/2500000) (δ := 1621/250000000) (ψ := -8717/31250) 128 109
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t212 : ((42355422741/1250000000000 : ℚ) : ℝ) ≤ stT128 212 := by
  have hc : ((123341/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42355422741/1250000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((123341/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c213 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-86237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1035713/2500000) (δ := 1621/250000000) (ψ := -8717/31250) 128 109
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t213 : ((-59122903243/10000000000000 : ℚ) : ℝ) ≤ stT128 213 := by
  have hc : ((-86287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59122903243/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-86287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c214 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-633357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56417/100000) (δ := 1621/250000000) (ψ := -8717/31250) 128 109
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t214 : ((-216494078751/5000000000000 : ℚ) : ℝ) ≤ stT128 214 := by
  have hc : ((-633407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-216494078751/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-633407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c215 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-239691/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 356677/500000) (δ := 1621/250000000) (ψ := -8717/31250) 128 109
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t215 : ((-65390635393/1000000000000 : ℚ) : ℝ) ≤ stT128 215 := by
  have hc : ((-479407/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65390635393/1000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-479407/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c216 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-119201/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1417899/2000000) (δ := 6591/1000000000) (ψ := -8717/31250) 128 110
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t216 : ((-162220563603/2500000000000 : ℚ) : ℝ) ≤ stT128 216 := by
  have hc : ((-476829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162220563603/2500000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-476829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c217 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-311973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5611447/10000000) (δ := 6591/1000000000) (ψ := -8717/31250) 128 110
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t217 : ((-21179828231/500000000000 : ℚ) : ℝ) ≤ stT128 217 := by
  have hc : ((-155999/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21179828231/500000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-155999/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c218 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-42587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4140183/10000000) (δ := 6591/1000000000) (ψ := -8717/31250) 128 110
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t218 : ((-3607563879/625000000000 : ℚ) : ℝ) ≤ stT128 218 := by
  have hc : ((-10653/125000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3607563879/625000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-10653/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c219 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((4799/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2675639/10000000) (δ := 6591/1000000000) (ψ := -8717/31250) 128 110
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t219 : ((6485047989/200000000000 : ℚ) : ℝ) ≤ stT128 219 := by
  have hc : ((9597/20000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6485047989/200000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((9597/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c220 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((110461/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1217783/10000000) (δ := 6591/1000000000) (ψ := -8717/31250) 128 110
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t220 : ((297873927981/5000000000000 : ℚ) : ℝ) ≤ stT128 220 := by
  have hc : ((441819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((297873927981/5000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((441819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c221 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((497821/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 233481/10000000) (δ := 6591/1000000000) (ψ := -8717/31250) 128 110
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t221 : ((2616042429/39062500000 : ℚ) : ℝ) ≤ stT128 221 := by
  have hc : ((124449/125000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2616042429/39062500000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((124449/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c222 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((391519/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1678153/10000000) (δ := 6591/1000000000) (ψ := -8717/31250) 128 110
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t222 : ((32844193383/625000000000 : ℚ) : ℝ) ≤ stT128 222 := by
  have hc : ((195747/250000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32844193383/625000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((195747/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c223 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((1593/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3116361/10000000) (δ := 6591/1000000000) (ψ := -8717/31250) 128 110
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t223 : ((4266333779/200000000000 : ℚ) : ℝ) ≤ stT128 223 := by
  have hc : ((6371/20000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4266333779/200000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((6371/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c224 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-24591/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4548137/10000000) (δ := 6591/1000000000) (ψ := -8717/31250) 128 110
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t224 : ((-2054239473/125000000000 : ℚ) : ℝ) ≤ stT128 224 := by
  have hc : ((-6149/25000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2054239473/125000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-6149/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c225 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-146041/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1194709/2000000) (δ := 6591/1000000000) (ψ := -8717/31250) 128 110
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t225 : ((-97367382017/2000000000000 : ℚ) : ℝ) ≤ stT128 225 := by
  have hc : ((-146051/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97367382017/2000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-146051/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c226 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-983019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7392601/10000000) (δ := 12991/1000000000) (ψ := -8717/31250) 128 110
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t226 : ((-653928651179/10000000000000 : ℚ) : ℝ) ≤ stT128 226 := by
  have hc : ((-983069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-653928651179/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-983069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c227 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-232113/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6902547/10000000) (δ := 1301/200000000) (ψ := -8717/31250) 128 111
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t227 : ((-77033632681/1250000000000 : ℚ) : ℝ) ≤ stT128 227 := by
  have hc : ((-464251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77033632681/1250000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-464251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c228 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-73399/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1099191/2000000) (δ := 1301/200000000) (ψ := -8717/31250) 128 111
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t228 : ((-194455498807/5000000000000 : ℚ) : ℝ) ≤ stT128 228 := by
  have hc : ((-293621/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194455498807/5000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-293621/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c229 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-13471/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4095507/10000000) (δ := 1301/200000000) (ψ := -8717/31250) 128 111
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t229 : ((-8908500939/2000000000000 : ℚ) : ℝ) ≤ stT128 229 := by
  have hc : ((-13481/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8908500939/2000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-13481/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c230 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((94183/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2701171/10000000) (δ := 1301/200000000) (ψ := -8717/31250) 128 111
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t230 : ((3104789637/100000000000 : ℚ) : ℝ) ≤ stT128 230 := by
  have hc : ((94173/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3104789637/100000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((94173/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c231 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((865247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1312883/10000000) (δ := 1301/200000000) (ψ := -8717/31250) 128 111
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t231 : ((569257231347/10000000000000 : ℚ) : ℝ) ≤ stT128 231 := by
  have hc : ((865197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((569257231347/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((865197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c232 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((199923/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69389/10000000) (δ := 1301/200000000) (ψ := -8717/31250) 128 111
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t232 : ((32812320429/500000000000 : ℚ) : ℝ) ≤ stT128 232 := by
  have hc : ((199913/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32812320429/500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((199913/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c233 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((167479/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1445741/10000000) (δ := 1301/200000000) (ψ := -8717/31250) 128 111
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t233 : ((109712458749/2000000000000 : ℚ) : ℝ) ≤ stT128 233 := by
  have hc : ((167469/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109712458749/2000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((167469/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c234 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((429839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 563241/2000000) (δ := 1301/200000000) (ψ := -8717/31250) 128 111
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t234 : ((7024041627/250000000000 : ℚ) : ℝ) ≤ stT128 234 := by
  have hc : ((429789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7024041627/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((429789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c235 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-20271/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4180813/10000000) (δ := 1301/200000000) (ψ := -8717/31250) 128 111
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t235 : ((-13229884449/2000000000000 : ℚ) : ℝ) ≤ stT128 235 := by
  have hc : ((-20281/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13229884449/2000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-20281/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c236 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-601243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5539629/10000000) (δ := 1301/200000000) (ψ := -8717/31250) 128 111
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t236 : ((-78281734377/2000000000000 : ℚ) : ℝ) ≤ stT128 236 := by
  have hc : ((-601293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78281734377/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-601293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c237 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-926979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1378537/2000000) (δ := 1301/200000000) (ψ := -8717/31250) 128 111
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t237 : ((-60217022753/1000000000000 : ℚ) : ℝ) ≤ stT128 237 := by
  have hc : ((-927029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60217022753/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-927029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c238 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-9881/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3733959/5000000) (δ := 3203/500000000) (ψ := -8717/31250) 128 112
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t238 : ((-3202613913/50000000000 : ℚ) : ℝ) ≤ stT128 238 := by
  have hc : ((-19763/20000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3202613913/50000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-19763/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c239 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-154107/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -612619/1000000) (δ := 3203/500000000) (ψ := -8717/31250) 128 112
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t239 : ((-99690119099/2000000000000 : ℚ) : ℝ) ≤ stT128 239 := by
  have hc : ((-154117/200000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99690119099/2000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-154117/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c240 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-84603/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2395031/5000000) (δ := 3203/500000000) (ψ := -8717/31250) 128 112
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t240 : ((-54619136019/2500000000000 : ℚ) : ℝ) ≤ stT128 240 := by
  have hc : ((-169231/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54619136019/2500000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-169231/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c241 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((46477/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1729751/5000000) (δ := 3203/500000000) (ψ := -8717/31250) 128 112
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t241 : ((14965193231/1250000000000 : ℚ) : ℝ) ≤ stT128 241 := by
  have hc : ((92929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14965193231/1250000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((92929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c242 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((32857/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1067223/5000000) (δ := 3203/500000000) (ψ := -8717/31250) 128 112
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t242 : ((5279915277/125000000000 : ℚ) : ℝ) ≤ stT128 242 := by
  have hc : ((65709/100000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5279915277/125000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((65709/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c243 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((947349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -407431/5000000) (δ := 3203/500000000) (ψ := -8717/31250) 128 112
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t243 : ((1215384617/20000000000 : ℚ) : ℝ) ≤ stT128 243 := by
  have hc : ((947299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1215384617/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((947299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c244 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((980121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 249657/5000000) (δ := 3203/500000000) (ψ := -8717/31250) 128 112
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t244 : ((78428221633/1250000000000 : ℚ) : ℝ) ≤ stT128 244 := by
  have hc : ((980071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78428221633/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((980071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c245 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((374833/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 904049/5000000) (δ := 6403/500000000) (ψ := -8717/31250) 128 112
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t245 : ((7482994869/156250000000 : ℚ) : ℝ) ≤ stT128 245 := by
  have hc : ((46851/62500 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7482994869/156250000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((46851/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c246 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((10013/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 311157/1000000) (δ := 3203/500000000) (ψ := -8717/31250) 128 112
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t246 : ((12766104551/625000000000 : ℚ) : ℝ) ≤ stT128 246 := by
  have hc : ((160183/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12766104551/625000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((160183/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c247 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-5997/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2204873/5000000) (δ := 3203/500000000) (ψ := -8717/31250) 128 112
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t247 : ((-12213745089/1000000000000 : ℚ) : ℝ) ≤ stT128 247 := by
  have hc : ((-95977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12213745089/1000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-95977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c248 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-652041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2851337/5000000) (δ := 3203/500000000) (ψ := -8717/31250) 128 112
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t248 : ((-414078437091/10000000000000 : ℚ) : ℝ) ≤ stT128 248 := by
  have hc : ((-652091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-414078437091/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-652091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c249 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-940927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3495193/5000000) (δ := 3203/500000000) (ψ := -8717/31250) 128 112
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t249 : ((-23852825973/400000000000 : ℚ) : ℝ) ≤ stT128 249 := by
  have hc : ((-940977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23852825973/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-940977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_c250 :
    |Real.cos (((128 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-246497/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1486997/2000000) (δ := 6513/1000000000) (ψ := -8717/31250) 128 113
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st128_t250 : ((-38976603083/625000000000 : ℚ) : ℝ) ≤ stT128 250 := by
  have hc : ((-493019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((128 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st128_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38976603083/625000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-493019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st128_p1 : ((961297/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT128 (i+1) := by
  rw [Finset.sum_range_one]
  exact st128_t1

theorem st128_p2 : ((3302321597983/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT128 (i+1))
      = (∑ i ∈ Finset.range 1, stT128 (i+1)) + stT128 2 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 1
    simpa using h
  have hprev := st128_p1
  have hstep := st128_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p3 : ((2015615625391/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT128 (i+1))
      = (∑ i ∈ Finset.range 2, stT128 (i+1)) + stT128 3 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 2
    simpa using h
  have hprev := st128_p2
  have hstep := st128_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p4 : ((6948457278763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT128 (i+1))
      = (∑ i ∈ Finset.range 3, stT128 (i+1)) + stT128 4 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 3
    simpa using h
  have hprev := st128_p3
  have hstep := st128_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p5 : ((285684122369/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT128 (i+1))
      = (∑ i ∈ Finset.range 4, stT128 (i+1)) + stT128 5 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 4
    simpa using h
  have hprev := st128_p4
  have hstep := st128_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p6 : ((5227219379523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT128 (i+1))
      = (∑ i ∈ Finset.range 5, stT128 (i+1)) + stT128 6 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 5
    simpa using h
  have hprev := st128_p5
  have hstep := st128_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p7 : ((3751086584063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT128 (i+1))
      = (∑ i ∈ Finset.range 6, stT128 (i+1)) + stT128 7 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 6
    simpa using h
  have hprev := st128_p6
  have hstep := st128_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p8 : ((808991965963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT128 (i+1))
      = (∑ i ∈ Finset.range 7, stT128 (i+1)) + stT128 8 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 7
    simpa using h
  have hprev := st128_p7
  have hstep := st128_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p9 : ((1955398517989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT128 (i+1))
      = (∑ i ∈ Finset.range 8, stT128 (i+1)) + stT128 9 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 8
    simpa using h
  have hprev := st128_p8
  have hstep := st128_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p10 : ((4976391306183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT128 (i+1))
      = (∑ i ∈ Finset.range 9, stT128 (i+1)) + stT128 10 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 9
    simpa using h
  have hprev := st128_p9
  have hstep := st128_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p11 : ((918250976169/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT128 (i+1))
      = (∑ i ∈ Finset.range 10, stT128 (i+1)) + stT128 11 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 10
    simpa using h
  have hprev := st128_p10
  have hstep := st128_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p12 : ((737479679177/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT128 (i+1))
      = (∑ i ∈ Finset.range 11, stT128 (i+1)) + stT128 12 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 11
    simpa using h
  have hprev := st128_p11
  have hstep := st128_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p13 : ((2545300976321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT128 (i+1))
      = (∑ i ∈ Finset.range 12, stT128 (i+1)) + stT128 13 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 12
    simpa using h
  have hprev := st128_p12
  have hstep := st128_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p14 : ((3012319878731/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT128 (i+1))
      = (∑ i ∈ Finset.range 13, stT128 (i+1)) + stT128 14 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 13
    simpa using h
  have hprev := st128_p13
  have hstep := st128_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p15 : ((662975704713/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT128 (i+1))
      = (∑ i ∈ Finset.range 14, stT128 (i+1)) + stT128 15 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 14
    simpa using h
  have hprev := st128_p14
  have hstep := st128_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p16 : ((260363191347/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT128 (i+1))
      = (∑ i ∈ Finset.range 15, stT128 (i+1)) + stT128 16 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 15
    simpa using h
  have hprev := st128_p15
  have hstep := st128_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p17 : ((1087641851391/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT128 (i+1))
      = (∑ i ∈ Finset.range 16, stT128 (i+1)) + stT128 17 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 16
    simpa using h
  have hprev := st128_p16
  have hstep := st128_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p18 : ((161524826247/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT128 (i+1))
      = (∑ i ∈ Finset.range 17, stT128 (i+1)) + stT128 18 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 17
    simpa using h
  have hprev := st128_p17
  have hstep := st128_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p19 : ((435979530819/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT128 (i+1))
      = (∑ i ∈ Finset.range 18, stT128 (i+1)) + stT128 19 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 18
    simpa using h
  have hprev := st128_p18
  have hstep := st128_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p20 : ((5362365016511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT128 (i+1))
      = (∑ i ∈ Finset.range 19, stT128 (i+1)) + stT128 20 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 19
    simpa using h
  have hprev := st128_p19
  have hstep := st128_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p21 : ((794803202507/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT128 (i+1))
      = (∑ i ∈ Finset.range 20, stT128 (i+1)) + stT128 21 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 20
    simpa using h
  have hprev := st128_p20
  have hstep := st128_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p22 : ((3709948236587/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT128 (i+1))
      = (∑ i ∈ Finset.range 21, stT128 (i+1)) + stT128 22 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 21
    simpa using h
  have hprev := st128_p21
  have hstep := st128_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p23 : ((4166980524227/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT128 (i+1))
      = (∑ i ∈ Finset.range 22, stT128 (i+1)) + stT128 23 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 22
    simpa using h
  have hprev := st128_p22
  have hstep := st128_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p24 : ((2142538261141/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT128 (i+1))
      = (∑ i ∈ Finset.range 23, stT128 (i+1)) + stT128 24 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 23
    simpa using h
  have hprev := st128_p23
  have hstep := st128_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p25 : ((313438987099/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT128 (i+1))
      = (∑ i ∈ Finset.range 24, stT128 (i+1)) + stT128 25 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 24
    simpa using h
  have hprev := st128_p24
  have hstep := st128_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p26 : ((3491634151971/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT128 (i+1))
      = (∑ i ∈ Finset.range 25, stT128 (i+1)) + stT128 26 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 25
    simpa using h
  have hprev := st128_p25
  have hstep := st128_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p27 : ((459768684387/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT128 (i+1))
      = (∑ i ∈ Finset.range 26, stT128 (i+1)) + stT128 27 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 26
    simpa using h
  have hprev := st128_p26
  have hstep := st128_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p28 : ((4102415459007/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT128 (i+1))
      = (∑ i ∈ Finset.range 27, stT128 (i+1)) + stT128 28 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 27
    simpa using h
  have hprev := st128_p27
  have hstep := st128_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p29 : ((1905932182983/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT128 (i+1))
      = (∑ i ∈ Finset.range 28, stT128 (i+1)) + stT128 29 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 28
    simpa using h
  have hprev := st128_p28
  have hstep := st128_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p30 : ((1433762267281/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT128 (i+1))
      = (∑ i ∈ Finset.range 29, stT128 (i+1)) + stT128 30 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 29
    simpa using h
  have hprev := st128_p29
  have hstep := st128_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p31 : ((161335499491/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT128 (i+1))
      = (∑ i ∈ Finset.range 30, stT128 (i+1)) + stT128 31 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 30
    simpa using h
  have hprev := st128_p30
  have hstep := st128_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p32 : ((15074620392993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT128 (i+1))
      = (∑ i ∈ Finset.range 31, stT128 (i+1)) + stT128 32 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 31
    simpa using h
  have hprev := st128_p31
  have hstep := st128_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p33 : ((14805865313517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT128 (i+1))
      = (∑ i ∈ Finset.range 32, stT128 (i+1)) + stT128 33 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 32
    simpa using h
  have hprev := st128_p32
  have hstep := st128_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p34 : ((16076573159357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT128 (i+1))
      = (∑ i ∈ Finset.range 33, stT128 (i+1)) + stT128 34 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 33
    simpa using h
  have hprev := st128_p33
  have hstep := st128_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p35 : ((1801227326909/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT128 (i+1))
      = (∑ i ∈ Finset.range 34, stT128 (i+1)) + stT128 35 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 34
    simpa using h
  have hprev := st128_p34
  have hstep := st128_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p36 : ((8001754822231/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT128 (i+1))
      = (∑ i ∈ Finset.range 35, stT128 (i+1)) + stT128 36 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 35
    simpa using h
  have hprev := st128_p35
  have hstep := st128_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p37 : ((1838378897829/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT128 (i+1))
      = (∑ i ∈ Finset.range 36, stT128 (i+1)) + stT128 37 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 36
    simpa using h
  have hprev := st128_p36
  have hstep := st128_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p38 : ((7835609203371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT128 (i+1))
      = (∑ i ∈ Finset.range 37, stT128 (i+1)) + stT128 38 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 37
    simpa using h
  have hprev := st128_p37
  have hstep := st128_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p39 : ((7484965274857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT128 (i+1))
      = (∑ i ∈ Finset.range 38, stT128 (i+1)) + stT128 39 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 38
    simpa using h
  have hprev := st128_p38
  have hstep := st128_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p40 : ((12414579949/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT128 (i+1))
      = (∑ i ∈ Finset.range 39, stT128 (i+1)) + stT128 40 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 39
    simpa using h
  have hprev := st128_p39
  have hstep := st128_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p41 : ((1875564721337/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT128 (i+1))
      = (∑ i ∈ Finset.range 40, stT128 (i+1)) + stT128 41 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 40
    simpa using h
  have hprev := st128_p40
  have hstep := st128_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p42 : ((15594251095999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT128 (i+1))
      = (∑ i ∈ Finset.range 41, stT128 (i+1)) + stT128 42 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 41
    simpa using h
  have hprev := st128_p41
  have hstep := st128_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p43 : ((14833914426203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT128 (i+1))
      = (∑ i ∈ Finset.range 42, stT128 (i+1)) + stT128 43 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 42
    simpa using h
  have hprev := st128_p42
  have hstep := st128_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p44 : ((15828856159523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT128 (i+1))
      = (∑ i ∈ Finset.range 43, stT128 (i+1)) + stT128 44 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 43
    simpa using h
  have hprev := st128_p43
  have hstep := st128_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p45 : ((14585855772563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT128 (i+1))
      = (∑ i ∈ Finset.range 44, stT128 (i+1)) + stT128 45 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 44
    simpa using h
  have hprev := st128_p44
  have hstep := st128_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p46 : ((1601193299681/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT128 (i+1))
      = (∑ i ∈ Finset.range 45, stT128 (i+1)) + stT128 46 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 45
    simpa using h
  have hprev := st128_p45
  have hstep := st128_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p47 : ((1456593824421/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT128 (i+1))
      = (∑ i ∈ Finset.range 46, stT128 (i+1)) + stT128 47 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 46
    simpa using h
  have hprev := st128_p46
  have hstep := st128_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p48 : ((788700856923/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT128 (i+1))
      = (∑ i ∈ Finset.range 47, stT128 (i+1)) + stT128 48 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 47
    simpa using h
  have hprev := st128_p47
  have hstep := st128_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p49 : ((377556314601/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT128 (i+1))
      = (∑ i ∈ Finset.range 48, stT128 (i+1)) + stT128 49 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 48
    simpa using h
  have hprev := st128_p48
  have hstep := st128_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p50 : ((300174470823/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT128 (i+1))
      = (∑ i ∈ Finset.range 49, stT128 (i+1)) + stT128 50 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 49
    simpa using h
  have hprev := st128_p49
  have hstep := st128_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p51 : ((317629801191/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT128 (i+1))
      = (∑ i ∈ Finset.range 50, stT128 (i+1)) + stT128 51 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 50
    simpa using h
  have hprev := st128_p50
  have hstep := st128_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p52 : ((7267494060287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT128 (i+1))
      = (∑ i ∈ Finset.range 51, stT128 (i+1)) + stT128 52 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 51
    simpa using h
  have hprev := st128_p51
  have hstep := st128_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p53 : ((7882352624807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT128 (i+1))
      = (∑ i ∈ Finset.range 52, stT128 (i+1)) + stT128 53 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 52
    simpa using h
  have hprev := st128_p52
  have hstep := st128_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p54 : ((7642565205411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT128 (i+1))
      = (∑ i ∈ Finset.range 53, stT128 (i+1)) + stT128 54 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 53
    simpa using h
  have hprev := st128_p53
  have hstep := st128_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p55 : ((7359755160411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT128 (i+1))
      = (∑ i ∈ Finset.range 54, stT128 (i+1)) + stT128 55 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 54
    simpa using h
  have hprev := st128_p54
  have hstep := st128_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p56 : ((3998742574931/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT128 (i+1))
      = (∑ i ∈ Finset.range 55, stT128 (i+1)) + stT128 56 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 55
    simpa using h
  have hprev := st128_p55
  have hstep := st128_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p57 : ((7441066055491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT128 (i+1))
      = (∑ i ∈ Finset.range 56, stT128 (i+1)) + stT128 57 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 56
    simpa using h
  have hprev := st128_p56
  have hstep := st128_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p58 : ((7494854409187/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT128 (i+1))
      = (∑ i ∈ Finset.range 57, stT128 (i+1)) + stT128 58 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 57
    simpa using h
  have hprev := st128_p57
  have hstep := st128_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p59 : ((3996480523127/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT128 (i+1))
      = (∑ i ∈ Finset.range 58, stT128 (i+1)) + stT128 59 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 58
    simpa using h
  have hprev := st128_p58
  have hstep := st128_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p60 : ((1843639091831/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT128 (i+1))
      = (∑ i ∈ Finset.range 59, stT128 (i+1)) + stT128 60 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 59
    simpa using h
  have hprev := st128_p59
  have hstep := st128_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p61 : ((376770257903/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT128 (i+1))
      = (∑ i ∈ Finset.range 60, stT128 (i+1)) + stT128 61 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 60
    simpa using h
  have hprev := st128_p60
  have hstep := st128_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p62 : ((15987277327747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT128 (i+1))
      = (∑ i ∈ Finset.range 61, stT128 (i+1)) + stT128 62 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 61
    simpa using h
  have hprev := st128_p61
  have hstep := st128_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p63 : ((14794890986133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT128 (i+1))
      = (∑ i ∈ Finset.range 62, stT128 (i+1)) + stT128 63 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 62
    simpa using h
  have hprev := st128_p62
  have hstep := st128_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p64 : ((14939527236133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT128 (i+1))
      = (∑ i ∈ Finset.range 63, stT128 (i+1)) + stT128 64 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 63
    simpa using h
  have hprev := st128_p63
  have hstep := st128_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p65 : ((16009795374799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT128 (i+1))
      = (∑ i ∈ Finset.range 64, stT128 (i+1)) + stT128 65 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 64
    simpa using h
  have hprev := st128_p64
  have hstep := st128_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p66 : ((15035506457659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT128 (i+1))
      = (∑ i ∈ Finset.range 65, stT128 (i+1)) + stT128 66 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 65
    simpa using h
  have hprev := st128_p65
  have hstep := st128_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p67 : ((7335142201247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT128 (i+1))
      = (∑ i ∈ Finset.range 66, stT128 (i+1)) + stT128 67 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 66
    simpa using h
  have hprev := st128_p66
  have hstep := st128_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p68 : ((7941304150259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT128 (i+1))
      = (∑ i ∈ Finset.range 67, stT128 (i+1)) + stT128 68 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 67
    simpa using h
  have hprev := st128_p67
  have hstep := st128_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p69 : ((1938003243169/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT128 (i+1))
      = (∑ i ∈ Finset.range 68, stT128 (i+1)) + stT128 69 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 68
    simpa using h
  have hprev := st128_p68
  have hstep := st128_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p70 : ((14511339256463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT128 (i+1))
      = (∑ i ∈ Finset.range 69, stT128 (i+1)) + stT128 70 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 69
    simpa using h
  have hprev := st128_p69
  have hstep := st128_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p71 : ((15391546241419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT128 (i+1))
      = (∑ i ∈ Finset.range 70, stT128 (i+1)) + stT128 71 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 70
    simpa using h
  have hprev := st128_p70
  have hstep := st128_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p72 : ((15972670015519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT128 (i+1))
      = (∑ i ∈ Finset.range 71, stT128 (i+1)) + stT128 72 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 71
    simpa using h
  have hprev := st128_p71
  have hstep := st128_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p73 : ((14861968924523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT128 (i+1))
      = (∑ i ∈ Finset.range 72, stT128 (i+1)) + stT128 73 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 72
    simpa using h
  have hprev := st128_p72
  have hstep := st128_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p74 : ((14687915893221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT128 (i+1))
      = (∑ i ∈ Finset.range 73, stT128 (i+1)) + stT128 74 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 73
    simpa using h
  have hprev := st128_p73
  have hstep := st128_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p75 : ((15842553539421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT128 (i+1))
      = (∑ i ∈ Finset.range 74, stT128 (i+1)) + stT128 75 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 74
    simpa using h
  have hprev := st128_p74
  have hstep := st128_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p76 : ((392580761779/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT128 (i+1))
      = (∑ i ∈ Finset.range 75, stT128 (i+1)) + stT128 76 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 75
    simpa using h
  have hprev := st128_p75
  have hstep := st128_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p77 : ((291841494699/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT128 (i+1))
      = (∑ i ∈ Finset.range 76, stT128 (i+1)) + stT128 77 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 76
    simpa using h
  have hprev := st128_p76
  have hstep := st128_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p78 : ((597280503891/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT128 (i+1))
      = (∑ i ∈ Finset.range 77, stT128 (i+1)) + stT128 78 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 77
    simpa using h
  have hprev := st128_p77
  have hstep := st128_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p79 : ((15983017118673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT128 (i+1))
      = (∑ i ∈ Finset.range 78, stT128 (i+1)) + stT128 79 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 78
    simpa using h
  have hprev := st128_p78
  have hstep := st128_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p80 : ((15543393851499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT128 (i+1))
      = (∑ i ∈ Finset.range 79, stT128 (i+1)) + stT128 80 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 79
    simpa using h
  have hprev := st128_p79
  have hstep := st128_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p81 : ((14530317485483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT128 (i+1))
      = (∑ i ∈ Finset.range 80, stT128 (i+1)) + stT128 81 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 80
    simpa using h
  have hprev := st128_p80
  have hstep := st128_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p82 : ((3745927091207/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT128 (i+1))
      = (∑ i ∈ Finset.range 81, stT128 (i+1)) + stT128 82 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 81
    simpa using h
  have hprev := st128_p81
  have hstep := st128_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p83 : ((7996493445451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT128 (i+1))
      = (∑ i ∈ Finset.range 82, stT128 (i+1)) + stT128 83 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 82
    simpa using h
  have hprev := st128_p82
  have hstep := st128_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p84 : ((7801214521611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT128 (i+1))
      = (∑ i ∈ Finset.range 83, stT128 (i+1)) + stT128 84 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 83
    simpa using h
  have hprev := st128_p83
  have hstep := st128_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p85 : ((14569434811653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT128 (i+1))
      = (∑ i ∈ Finset.range 84, stT128 (i+1)) + stT128 85 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 84
    simpa using h
  have hprev := st128_p84
  have hstep := st128_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p86 : ((14821851752467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT128 (i+1))
      = (∑ i ∈ Finset.range 85, stT128 (i+1)) + stT128 86 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 85
    simpa using h
  have hprev := st128_p85
  have hstep := st128_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p87 : ((635304360571/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT128 (i+1))
      = (∑ i ∈ Finset.range 86, stT128 (i+1)) + stT128 87 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 86
    simpa using h
  have hprev := st128_p86
  have hstep := st128_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p88 : ((15842694626503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT128 (i+1))
      = (∑ i ∈ Finset.range 87, stT128 (i+1)) + stT128 88 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 87
    simpa using h
  have hprev := st128_p87
  have hstep := st128_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p89 : ((14786657839029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT128 (i+1))
      = (∑ i ∈ Finset.range 88, stT128 (i+1)) + stT128 89 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 88
    simpa using h
  have hprev := st128_p88
  have hstep := st128_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p90 : ((1818585593657/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT128 (i+1))
      = (∑ i ∈ Finset.range 89, stT128 (i+1)) + stT128 90 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 89
    simpa using h
  have hprev := st128_p89
  have hstep := st128_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p91 : ((242508411919/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT128 (i+1))
      = (∑ i ∈ Finset.range 90, stT128 (i+1)) + stT128 91 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 90
    simpa using h
  have hprev := st128_p90
  have hstep := st128_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p92 : ((2008839775403/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT128 (i+1))
      = (∑ i ∈ Finset.range 91, stT128 (i+1)) + stT128 92 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 91
    simpa using h
  have hprev := st128_p91
  have hstep := st128_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p93 : ((1913373567237/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT128 (i+1))
      = (∑ i ∈ Finset.range 92, stT128 (i+1)) + stT128 93 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 92
    simpa using h
  have hprev := st128_p92
  have hstep := st128_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p94 : ((7235557433149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT128 (i+1))
      = (∑ i ∈ Finset.range 93, stT128 (i+1)) + stT128 94 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 93
    simpa using h
  have hprev := st128_p93
  have hstep := st128_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p95 : ((1487978652717/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT128 (i+1))
      = (∑ i ∈ Finset.range 94, stT128 (i+1)) + stT128 95 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 94
    simpa using h
  have hprev := st128_p94
  have hstep := st128_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p96 : ((1588399801943/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT128 (i+1))
      = (∑ i ∈ Finset.range 95, stT128 (i+1)) + stT128 96 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 95
    simpa using h
  have hprev := st128_p95
  have hstep := st128_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p97 : ((7974991662639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT128 (i+1))
      = (∑ i ∈ Finset.range 96, stT128 (i+1)) + stT128 97 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 96
    simpa using h
  have hprev := st128_p96
  have hstep := st128_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p98 : ((3748008253003/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT128 (i+1))
      = (∑ i ∈ Finset.range 97, stT128 (i+1)) + stT128 98 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 97
    simpa using h
  have hprev := st128_p97
  have hstep := st128_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p99 : ((450912552551/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT128 (i+1))
      = (∑ i ∈ Finset.range 98, stT128 (i+1)) + stT128 99 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 98
    simpa using h
  have hprev := st128_p98
  have hstep := st128_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p100 : ((7533653521763/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT128 (i+1))
      = (∑ i ∈ Finset.range 99, stT128 (i+1)) + stT128 100 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 99
    simpa using h
  have hprev := st128_p99
  have hstep := st128_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p101 : ((7992845186597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT128 (i+1))
      = (∑ i ∈ Finset.range 100, stT128 (i+1)) + stT128 101 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 100
    simpa using h
  have hprev := st128_p100
  have hstep := st128_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p102 : ((7950664881797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT128 (i+1))
      = (∑ i ∈ Finset.range 101, stT128 (i+1)) + stT128 102 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 101
    simpa using h
  have hprev := st128_p101
  have hstep := st128_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p103 : ((1867929781013/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT128 (i+1))
      = (∑ i ∈ Finset.range 102, stT128 (i+1)) + stT128 103 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 102
    simpa using h
  have hprev := st128_p102
  have hstep := st128_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p104 : ((14413546984419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT128 (i+1))
      = (∑ i ∈ Finset.range 103, stT128 (i+1)) + stT128 104 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 103
    simpa using h
  have hprev := st128_p103
  have hstep := st128_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p105 : ((15007249412019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT128 (i+1))
      = (∑ i ∈ Finset.range 104, stT128 (i+1)) + stT128 105 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 104
    simpa using h
  have hprev := st128_p104
  have hstep := st128_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p106 : ((15936093142659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT128 (i+1))
      = (∑ i ∈ Finset.range 105, stT128 (i+1)) + stT128 106 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 105
    simpa using h
  have hprev := st128_p105
  have hstep := st128_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p107 : ((16005939818659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT128 (i+1))
      = (∑ i ∈ Finset.range 106, stT128 (i+1)) + stT128 107 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 106
    simpa using h
  have hprev := st128_p106
  have hstep := st128_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p108 : ((15140464326231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT128 (i+1))
      = (∑ i ∈ Finset.range 107, stT128 (i+1)) + stT128 108 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 107
    simpa using h
  have hprev := st128_p107
  have hstep := st128_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p109 : ((3606232071581/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT128 (i+1))
      = (∑ i ∈ Finset.range 108, stT128 (i+1)) + stT128 109 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 108
    simpa using h
  have hprev := st128_p108
  have hstep := st128_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p110 : ((7364861218663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT128 (i+1))
      = (∑ i ∈ Finset.range 109, stT128 (i+1)) + stT128 110 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 109
    simpa using h
  have hprev := st128_p109
  have hstep := st128_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p111 : ((122462845047/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT128 (i+1))
      = (∑ i ∈ Finset.range 110, stT128 (i+1)) + stT128 111 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 110
    simpa using h
  have hprev := st128_p110
  have hstep := st128_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p112 : ((16136306874089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT128 (i+1))
      = (∑ i ∈ Finset.range 111, stT128 (i+1)) + stT128 112 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 111
    simpa using h
  have hprev := st128_p111
  have hstep := st128_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p113 : ((15583558028909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT128 (i+1))
      = (∑ i ∈ Finset.range 112, stT128 (i+1)) + stT128 113 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 112
    simpa using h
  have hprev := st128_p112
  have hstep := st128_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p114 : ((14662900547011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT128 (i+1))
      = (∑ i ∈ Finset.range 113, stT128 (i+1)) + stT128 114 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 113
    simpa using h
  have hprev := st128_p113
  have hstep := st128_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p115 : ((14415995603131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT128 (i+1))
      = (∑ i ∈ Finset.range 114, stT128 (i+1)) + stT128 115 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 114
    simpa using h
  have hprev := st128_p114
  have hstep := st128_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p116 : ((15107520814027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT128 (i+1))
      = (∑ i ∈ Finset.range 115, stT128 (i+1)) + stT128 116 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 115
    simpa using h
  have hprev := st128_p115
  have hstep := st128_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p117 : ((15969999807027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT128 (i+1))
      = (∑ i ∈ Finset.range 116, stT128 (i+1)) + stT128 117 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 116
    simpa using h
  have hprev := st128_p116
  have hstep := st128_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p118 : ((16073932611627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT128 (i+1))
      = (∑ i ∈ Finset.range 117, stT128 (i+1)) + stT128 118 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 117
    simpa using h
  have hprev := st128_p117
  have hstep := st128_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p119 : ((15319285827449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT128 (i+1))
      = (∑ i ∈ Finset.range 118, stT128 (i+1)) + stT128 119 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 118
    simpa using h
  have hprev := st128_p118
  have hstep := st128_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p120 : ((1450424812539/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT128 (i+1))
      = (∑ i ∈ Finset.range 119, stT128 (i+1)) + stT128 120 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 119
    simpa using h
  have hprev := st128_p119
  have hstep := st128_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p121 : ((7233365879001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT128 (i+1))
      = (∑ i ∈ Finset.range 120, stT128 (i+1)) + stT128 121 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 120
    simpa using h
  have hprev := st128_p120
  have hstep := st128_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p122 : ((609378581403/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT128 (i+1))
      = (∑ i ∈ Finset.range 121, stT128 (i+1)) + stT128 122 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 121
    simpa using h
  have hprev := st128_p121
  have hstep := st128_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p123 : ((3206304379539/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT128 (i+1))
      = (∑ i ∈ Finset.range 122, stT128 (i+1)) + stT128 123 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 122
    simpa using h
  have hprev := st128_p122
  have hstep := st128_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p124 : ((16074542731251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT128 (i+1))
      = (∑ i ∈ Finset.range 123, stT128 (i+1)) + stT128 124 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 123
    simpa using h
  have hprev := st128_p123
  have hstep := st128_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p125 : ((15331604001611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT128 (i+1))
      = (∑ i ∈ Finset.range 124, stT128 (i+1)) + stT128 125 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 124
    simpa using h
  have hprev := st128_p124
  have hstep := st128_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p126 : ((7260760819123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT128 (i+1))
      = (∑ i ∈ Finset.range 125, stT128 (i+1)) + stT128 126 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 125
    simpa using h
  have hprev := st128_p125
  have hstep := st128_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p127 : ((1800842751287/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT128 (i+1))
      = (∑ i ∈ Finset.range 126, stT128 (i+1)) + stT128 127 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 126
    simpa using h
  have hprev := st128_p126
  have hstep := st128_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p128 : ((3016940120121/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT128 (i+1))
      = (∑ i ∈ Finset.range 127, stT128 (i+1)) + stT128 128 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 127
    simpa using h
  have hprev := st128_p127
  have hstep := st128_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p129 : ((3185177738751/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT128 (i+1))
      = (∑ i ∈ Finset.range 128, stT128 (i+1)) + stT128 129 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 128
    simpa using h
  have hprev := st128_p128
  have hstep := st128_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p130 : ((16170573842827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT128 (i+1))
      = (∑ i ∈ Finset.range 129, stT128 (i+1)) + stT128 130 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 129
    simpa using h
  have hprev := st128_p129
  have hstep := st128_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p131 : ((7804484687201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT128 (i+1))
      = (∑ i ∈ Finset.range 130, stT128 (i+1)) + stT128 131 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 130
    simpa using h
  have hprev := st128_p130
  have hstep := st128_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p132 : ((14742941893681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT128 (i+1))
      = (∑ i ∈ Finset.range 131, stT128 (i+1)) + stT128 132 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 131
    simpa using h
  have hprev := st128_p131
  have hstep := st128_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p133 : ((14324067933091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT128 (i+1))
      = (∑ i ∈ Finset.range 132, stT128 (i+1)) + stT128 133 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 132
    simpa using h
  have hprev := st128_p132
  have hstep := st128_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p134 : ((14703432109819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT128 (i+1))
      = (∑ i ∈ Finset.range 133, stT128 (i+1)) + stT128 134 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 133
    simpa using h
  have hprev := st128_p133
  have hstep := st128_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p135 : ((15552444188987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT128 (i+1))
      = (∑ i ∈ Finset.range 134, stT128 (i+1)) + stT128 135 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 134
    simpa using h
  have hprev := st128_p134
  have hstep := st128_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p136 : ((3232372579179/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT128 (i+1))
      = (∑ i ∈ Finset.range 135, stT128 (i+1)) + stT128 136 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 135
    simpa using h
  have hprev := st128_p135
  have hstep := st128_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p137 : ((16036530286011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT128 (i+1))
      = (∑ i ∈ Finset.range 136, stT128 (i+1)) + stT128 137 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 136
    simpa using h
  have hprev := st128_p136
  have hstep := st128_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p138 : ((764324259477/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT128 (i+1))
      = (∑ i ∈ Finset.range 137, stT128 (i+1)) + stT128 138 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 137
    simpa using h
  have hprev := st128_p137
  have hstep := st128_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p139 : ((2903198908577/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT128 (i+1))
      = (∑ i ∈ Finset.range 138, stT128 (i+1)) + stT128 139 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 138
    simpa using h
  have hprev := st128_p138
  have hstep := st128_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p140 : ((716503909557/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT128 (i+1))
      = (∑ i ∈ Finset.range 139, stT128 (i+1)) + stT128 140 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 139
    simpa using h
  have hprev := st128_p139
  have hstep := st128_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p141 : ((3716408082369/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT128 (i+1))
      = (∑ i ∈ Finset.range 140, stT128 (i+1)) + stT128 141 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 140
    simpa using h
  have hprev := st128_p140
  have hstep := st128_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p142 : ((15704547309099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT128 (i+1))
      = (∑ i ∈ Finset.range 141, stT128 (i+1)) + stT128 142 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 141
    simpa using h
  have hprev := st128_p141
  have hstep := st128_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p143 : ((16210223682741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT128 (i+1))
      = (∑ i ∈ Finset.range 142, stT128 (i+1)) + stT128 143 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 142
    simpa using h
  have hprev := st128_p142
  have hstep := st128_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p144 : ((16010051022603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT128 (i+1))
      = (∑ i ∈ Finset.range 143, stT128 (i+1)) + stT128 144 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 143
    simpa using h
  have hprev := st128_p143
  have hstep := st128_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p145 : ((15259520672713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT128 (i+1))
      = (∑ i ∈ Finset.range 144, stT128 (i+1)) + stT128 145 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 144
    simpa using h
  have hprev := st128_p144
  have hstep := st128_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p146 : ((14509747706589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT128 (i+1))
      = (∑ i ∈ Finset.range 145, stT128 (i+1)) + stT128 146 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 145
    simpa using h
  have hprev := st128_p145
  have hstep := st128_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p147 : ((2859566706621/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT128 (i+1))
      = (∑ i ∈ Finset.range 146, stT128 (i+1)) + stT128 147 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 146
    simpa using h
  have hprev := st128_p146
  have hstep := st128_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p148 : ((14767342532007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT128 (i+1))
      = (∑ i ∈ Finset.range 147, stT128 (i+1)) + stT128 148 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 147
    simpa using h
  have hprev := st128_p147
  have hstep := st128_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p149 : ((15582372515439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT128 (i+1))
      = (∑ i ∈ Finset.range 148, stT128 (i+1)) + stT128 149 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 148
    simpa using h
  have hprev := st128_p148
  have hstep := st128_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p150 : ((16176763640527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT128 (i+1))
      = (∑ i ∈ Finset.range 149, stT128 (i+1)) + stT128 150 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 149
    simpa using h
  have hprev := st128_p149
  have hstep := st128_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p151 : ((16148191508737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT128 (i+1))
      = (∑ i ∈ Finset.range 150, stT128 (i+1)) + stT128 151 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 150
    simpa using h
  have hprev := st128_p150
  have hstep := st128_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p152 : ((15523021095549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT128 (i+1))
      = (∑ i ∈ Finset.range 151, stT128 (i+1)) + stT128 152 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 151
    simpa using h
  have hprev := st128_p151
  have hstep := st128_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p153 : ((1472342631507/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT128 (i+1))
      = (∑ i ∈ Finset.range 152, stT128 (i+1)) + stT128 153 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 152
    simpa using h
  have hprev := st128_p152
  have hstep := st128_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p154 : ((14276124443469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT128 (i+1))
      = (∑ i ∈ Finset.range 153, stT128 (i+1)) + stT128 154 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 153
    simpa using h
  have hprev := st128_p153
  have hstep := st128_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p155 : ((7233534036903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT128 (i+1))
      = (∑ i ∈ Finset.range 154, stT128 (i+1)) + stT128 155 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 154
    simpa using h
  have hprev := st128_p154
  have hstep := st128_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p156 : ((7583365278183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT128 (i+1))
      = (∑ i ∈ Finset.range 155, stT128 (i+1)) + stT128 156 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 155
    simpa using h
  have hprev := st128_p155
  have hstep := st128_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p157 : ((1592665527619/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT128 (i+1))
      = (∑ i ∈ Finset.range 156, stT128 (i+1)) + stT128 157 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 156
    simpa using h
  have hprev := st128_p156
  have hstep := st128_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p158 : ((16271059061503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT128 (i+1))
      = (∑ i ∈ Finset.range 157, stT128 (i+1)) + stT128 158 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 157
    simpa using h
  have hprev := st128_p157
  have hstep := st128_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p159 : ((15991792144119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT128 (i+1))
      = (∑ i ∈ Finset.range 158, stT128 (i+1)) + stT128 159 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 158
    simpa using h
  have hprev := st128_p158
  have hstep := st128_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p160 : ((15266226762369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT128 (i+1))
      = (∑ i ∈ Finset.range 159, stT128 (i+1)) + stT128 160 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 159
    simpa using h
  have hprev := st128_p159
  have hstep := st128_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p161 : ((3634240805657/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT128 (i+1))
      = (∑ i ∈ Finset.range 160, stT128 (i+1)) + stT128 161 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 160
    simpa using h
  have hprev := st128_p160
  have hstep := st128_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p162 : ((14238801917153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT128 (i+1))
      = (∑ i ∈ Finset.range 161, stT128 (i+1)) + stT128 162 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 161
    simpa using h
  have hprev := st128_p161
  have hstep := st128_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p163 : ((14542696614773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT128 (i+1))
      = (∑ i ∈ Finset.range 162, stT128 (i+1)) + stT128 163 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 162
    simpa using h
  have hprev := st128_p162
  have hstep := st128_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p164 : ((3053012240669/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT128 (i+1))
      = (∑ i ∈ Finset.range 163, stT128 (i+1)) + stT128 164 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 163
    simpa using h
  have hprev := st128_p163
  have hstep := st128_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p165 : ((15985448998633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT128 (i+1))
      = (∑ i ∈ Finset.range 164, stT128 (i+1)) + stT128 165 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 164
    simpa using h
  have hprev := st128_p164
  have hstep := st128_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p166 : ((16293859962633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT128 (i+1))
      = (∑ i ∈ Finset.range 165, stT128 (i+1)) + stT128 166 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 165
    simpa using h
  have hprev := st128_p165
  have hstep := st128_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p167 : ((3204231793653/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT128 (i+1))
      = (∑ i ∈ Finset.range 166, stT128 (i+1)) + stT128 167 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 166
    simpa using h
  have hprev := st128_p166
  have hstep := st128_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p168 : ((7662625702891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT128 (i+1))
      = (∑ i ∈ Finset.range 167, stT128 (i+1)) + stT128 168 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 167
    simpa using h
  have hprev := st128_p167
  have hstep := st128_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p169 : ((2918676852629/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT128 (i+1))
      = (∑ i ∈ Finset.range 168, stT128 (i+1)) + stT128 169 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 168
    simpa using h
  have hprev := st128_p168
  have hstep := st128_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p170 : ((711197589749/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT128 (i+1))
      = (∑ i ∈ Finset.range 169, stT128 (i+1)) + stT128 170 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 169
    simpa using h
  have hprev := st128_p169
  have hstep := st128_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p171 : ((14411787428793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT128 (i+1))
      = (∑ i ∈ Finset.range 170, stT128 (i+1)) + stT128 171 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 170
    simpa using h
  have hprev := st128_p170
  have hstep := st128_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p172 : ((3010223734197/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT128 (i+1))
      = (∑ i ∈ Finset.range 171, stT128 (i+1)) + stT128 172 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 171
    simpa using h
  have hprev := st128_p171
  have hstep := st128_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p173 : ((3160187821649/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT128 (i+1))
      = (∑ i ∈ Finset.range 172, stT128 (i+1)) + stT128 173 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 172
    simpa using h
  have hprev := st128_p172
  have hstep := st128_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p174 : ((16270025891509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT128 (i+1))
      = (∑ i ∈ Finset.range 173, stT128 (i+1)) + stT128 174 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 173
    simpa using h
  have hprev := st128_p173
  have hstep := st128_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p175 : ((16219912334383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT128 (i+1))
      = (∑ i ∈ Finset.range 174, stT128 (i+1)) + stT128 175 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 174
    simpa using h
  have hprev := st128_p174
  have hstep := st128_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p176 : ((7840721760861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT128 (i+1))
      = (∑ i ∈ Finset.range 175, stT128 (i+1)) + stT128 176 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 175
    simpa using h
  have hprev := st128_p175
  have hstep := st128_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p177 : ((14930696243181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT128 (i+1))
      = (∑ i ∈ Finset.range 176, stT128 (i+1)) + stT128 177 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 176
    simpa using h
  have hprev := st128_p176
  have hstep := st128_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p178 : ((573748519977/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT128 (i+1))
      = (∑ i ∈ Finset.range 177, stT128 (i+1)) + stT128 178 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 177
    simpa using h
  have hprev := st128_p177
  have hstep := st128_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p179 : ((14208014498753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT128 (i+1))
      = (∑ i ∈ Finset.range 178, stT128 (i+1)) + stT128 179 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 178
    simpa using h
  have hprev := st128_p178
  have hstep := st128_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p180 : ((7292574238149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT128 (i+1))
      = (∑ i ∈ Finset.range 179, stT128 (i+1)) + stT128 180 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 179
    simpa using h
  have hprev := st128_p179
  have hstep := st128_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p181 : ((764401962217/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT128 (i+1))
      = (∑ i ∈ Finset.range 180, stT128 (i+1)) + stT128 181 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 180
    simpa using h
  have hprev := st128_p180
  have hstep := st128_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p182 : ((3994492523393/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT128 (i+1))
      = (∑ i ∈ Finset.range 181, stT128 (i+1)) + stT128 182 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 181
    simpa using h
  have hprev := st128_p181
  have hstep := st128_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p183 : ((16329260479529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT128 (i+1))
      = (∑ i ∈ Finset.range 182, stT128 (i+1)) + stT128 183 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 182
    simpa using h
  have hprev := st128_p182
  have hstep := st128_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p184 : ((16181114443979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT128 (i+1))
      = (∑ i ∈ Finset.range 183, stT128 (i+1)) + stT128 184 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 183
    simpa using h
  have hprev := st128_p183
  have hstep := st128_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p185 : ((15606971816609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT128 (i+1))
      = (∑ i ∈ Finset.range 184, stT128 (i+1)) + stT128 185 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 184
    simpa using h
  have hprev := st128_p184
  have hstep := st128_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p186 : ((14873784943421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT128 (i+1))
      = (∑ i ∈ Finset.range 185, stT128 (i+1)) + stT128 186 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 185
    simpa using h
  have hprev := st128_p185
  have hstep := st128_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p187 : ((14315202062371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT128 (i+1))
      = (∑ i ∈ Finset.range 186, stT128 (i+1)) + stT128 187 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 186
    simpa using h
  have hprev := st128_p186
  have hstep := st128_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p188 : ((14179921026771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT128 (i+1))
      = (∑ i ∈ Finset.range 187, stT128 (i+1)) + stT128 188 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 187
    simpa using h
  have hprev := st128_p187
  have hstep := st128_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p189 : ((14523839965683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT128 (i+1))
      = (∑ i ∈ Finset.range 188, stT128 (i+1)) + stT128 189 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 188
    simpa using h
  have hprev := st128_p188
  have hstep := st128_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p190 : ((15191216220223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT128 (i+1))
      = (∑ i ∈ Finset.range 189, stT128 (i+1)) + stT128 190 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 189
    simpa using h
  have hprev := st128_p189
  have hstep := st128_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p191 : ((15888709718967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT128 (i+1))
      = (∑ i ∈ Finset.range 190, stT128 (i+1)) + stT128 191 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 190
    simpa using h
  have hprev := st128_p190
  have hstep := st128_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p192 : ((16315759340973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT128 (i+1))
      = (∑ i ∈ Finset.range 191, stT128 (i+1)) + stT128 192 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 191
    simpa using h
  have hprev := st128_p191
  have hstep := st128_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p193 : ((16292938294509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT128 (i+1))
      = (∑ i ∈ Finset.range 192, stT128 (i+1)) + stT128 193 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 192
    simpa using h
  have hprev := st128_p192
  have hstep := st128_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p194 : ((3958536495113/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT128 (i+1))
      = (∑ i ∈ Finset.range 193, stT128 (i+1)) + stT128 194 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 193
    simpa using h
  have hprev := st128_p193
  have hstep := st128_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p195 : ((15135182650817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT128 (i+1))
      = (∑ i ∈ Finset.range 194, stT128 (i+1)) + stT128 195 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 194
    simpa using h
  have hprev := st128_p194
  have hstep := st128_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p196 : ((14487442391721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT128 (i+1))
      = (∑ i ∈ Finset.range 195, stT128 (i+1)) + stT128 196 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 195
    simpa using h
  have hprev := st128_p195
  have hstep := st128_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p197 : ((14155755792497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT128 (i+1))
      = (∑ i ∈ Finset.range 196, stT128 (i+1)) + stT128 197 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 196
    simpa using h
  have hprev := st128_p196
  have hstep := st128_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p198 : ((713584254723/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT128 (i+1))
      = (∑ i ∈ Finset.range 197, stT128 (i+1)) + stT128 198 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 197
    simpa using h
  have hprev := st128_p197
  have hstep := st128_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p199 : ((14784470470073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT128 (i+1))
      = (∑ i ∈ Finset.range 198, stT128 (i+1)) + stT128 199 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 198
    simpa using h
  have hprev := st128_p198
  have hstep := st128_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p200 : ((15486418131803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT128 (i+1))
      = (∑ i ∈ Finset.range 199, stT128 (i+1)) + stT128 200 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 199
    simpa using h
  have hprev := st128_p199
  have hstep := st128_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p201 : ((8049603527779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT128 (i+1))
      = (∑ i ∈ Finset.range 200, stT128 (i+1)) + stT128 201 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 200
    simpa using h
  have hprev := st128_p200
  have hstep := st128_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p202 : ((8192266262693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT128 (i+1))
      = (∑ i ∈ Finset.range 201, stT128 (i+1)) + stT128 202 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 201
    simpa using h
  have hprev := st128_p201
  have hstep := st128_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p203 : ((16235102383371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT128 (i+1))
      = (∑ i ∈ Finset.range 202, stT128 (i+1)) + stT128 203 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 202
    simpa using h
  have hprev := st128_p202
  have hstep := st128_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p204 : ((7856042576987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT128 (i+1))
      = (∑ i ∈ Finset.range 203, stT128 (i+1)) + stT128 204 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 203
    simpa using h
  have hprev := st128_p203
  have hstep := st128_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p205 : ((15017205675609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT128 (i+1))
      = (∑ i ∈ Finset.range 204, stT128 (i+1)) + stT128 205 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 204
    simpa using h
  have hprev := st128_p204
  have hstep := st128_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p206 : ((14413046722189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT128 (i+1))
      = (∑ i ∈ Finset.range 205, stT128 (i+1)) + stT128 206 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 205
    simpa using h
  have hprev := st128_p205
  have hstep := st128_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p207 : ((14123608857217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT128 (i+1))
      = (∑ i ∈ Finset.range 206, stT128 (i+1)) + stT128 207 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 206
    simpa using h
  have hprev := st128_p206
  have hstep := st128_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p208 : ((7126380869171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT128 (i+1))
      = (∑ i ∈ Finset.range 207, stT128 (i+1)) + stT128 208 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 207
    simpa using h
  have hprev := st128_p207
  have hstep := st128_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p209 : ((921848174553/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT128 (i+1))
      = (∑ i ∈ Finset.range 208, stT128 (i+1)) + stT128 209 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 208
    simpa using h
  have hprev := st128_p208
  have hstep := st128_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p210 : ((15430952704953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT128 (i+1))
      = (∑ i ∈ Finset.range 209, stT128 (i+1)) + stT128 210 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 209
    simpa using h
  have hprev := st128_p209
  have hstep := st128_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p211 : ((16050934439481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT128 (i+1))
      = (∑ i ∈ Finset.range 210, stT128 (i+1)) + stT128 211 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 210
    simpa using h
  have hprev := st128_p210
  have hstep := st128_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p212 : ((16389777821409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT128 (i+1))
      = (∑ i ∈ Finset.range 211, stT128 (i+1)) + stT128 212 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 211
    simpa using h
  have hprev := st128_p211
  have hstep := st128_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p213 : ((8165327459083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT128 (i+1))
      = (∑ i ∈ Finset.range 212, stT128 (i+1)) + stT128 213 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 212
    simpa using h
  have hprev := st128_p212
  have hstep := st128_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p214 : ((1987208345083/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT128 (i+1))
      = (∑ i ∈ Finset.range 213, stT128 (i+1)) + stT128 214 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 213
    simpa using h
  have hprev := st128_p213
  have hstep := st128_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p215 : ((7621880203367/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT128 (i+1))
      = (∑ i ∈ Finset.range 214, stT128 (i+1)) + stT128 215 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 214
    simpa using h
  have hprev := st128_p214
  have hstep := st128_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p216 : ((7297439076161/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT128 (i+1))
      = (∑ i ∈ Finset.range 215, stT128 (i+1)) + stT128 216 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 215
    simpa using h
  have hprev := st128_p215
  have hstep := st128_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p217 : ((7085640793851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT128 (i+1))
      = (∑ i ∈ Finset.range 216, stT128 (i+1)) + stT128 217 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 216
    simpa using h
  have hprev := st128_p216
  have hstep := st128_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p218 : ((7056780282819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT128 (i+1))
      = (∑ i ∈ Finset.range 217, stT128 (i+1)) + stT128 218 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 217
    simpa using h
  have hprev := st128_p217
  have hstep := st128_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p219 : ((451181655159/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT128 (i+1))
      = (∑ i ∈ Finset.range 218, stT128 (i+1)) + stT128 219 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 218
    simpa using h
  have hprev := st128_p218
  have hstep := st128_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p220 : ((300671216421/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT128 (i+1))
      = (∑ i ∈ Finset.range 219, stT128 (i+1)) + stT128 220 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 219
    simpa using h
  have hprev := st128_p219
  have hstep := st128_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p221 : ((7851633841437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT128 (i+1))
      = (∑ i ∈ Finset.range 220, stT128 (i+1)) + stT128 221 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 220
    simpa using h
  have hprev := st128_p220
  have hstep := st128_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p222 : ((8114387388501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT128 (i+1))
      = (∑ i ∈ Finset.range 221, stT128 (i+1)) + stT128 222 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 221
    simpa using h
  have hprev := st128_p221
  have hstep := st128_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p223 : ((513815358311/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT128 (i+1))
      = (∑ i ∈ Finset.range 222, stT128 (i+1)) + stT128 223 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 222
    simpa using h
  have hprev := st128_p222
  have hstep := st128_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p224 : ((1017359519257/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT128 (i+1))
      = (∑ i ∈ Finset.range 223, stT128 (i+1)) + stT128 224 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 223
    simpa using h
  have hprev := st128_p223
  have hstep := st128_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p225 : ((15790915398027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT128 (i+1))
      = (∑ i ∈ Finset.range 224, stT128 (i+1)) + stT128 225 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 224
    simpa using h
  have hprev := st128_p224
  have hstep := st128_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p226 : ((473030835839/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT128 (i+1))
      = (∑ i ∈ Finset.range 225, stT128 (i+1)) + stT128 226 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 225
    simpa using h
  have hprev := st128_p225
  have hstep := st128_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p227 : ((72603588427/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT128 (i+1))
      = (∑ i ∈ Finset.range 226, stT128 (i+1)) + stT128 227 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 226
    simpa using h
  have hprev := st128_p226
  have hstep := st128_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p228 : ((7065903343893/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT128 (i+1))
      = (∑ i ∈ Finset.range 227, stT128 (i+1)) + stT128 228 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 227
    simpa using h
  have hprev := st128_p227
  have hstep := st128_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p229 : ((14087264183091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT128 (i+1))
      = (∑ i ∈ Finset.range 228, stT128 (i+1)) + stT128 229 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 228
    simpa using h
  have hprev := st128_p228
  have hstep := st128_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p230 : ((14397743146791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT128 (i+1))
      = (∑ i ∈ Finset.range 229, stT128 (i+1)) + stT128 230 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 229
    simpa using h
  have hprev := st128_p229
  have hstep := st128_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p231 : ((7483500189069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT128 (i+1))
      = (∑ i ∈ Finset.range 230, stT128 (i+1)) + stT128 231 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 230
    simpa using h
  have hprev := st128_p230
  have hstep := st128_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p232 : ((7811623393359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT128 (i+1))
      = (∑ i ∈ Finset.range 231, stT128 (i+1)) + stT128 232 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 231
    simpa using h
  have hprev := st128_p231
  have hstep := st128_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p233 : ((16171809080463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT128 (i+1))
      = (∑ i ∈ Finset.range 232, stT128 (i+1)) + stT128 233 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 232
    simpa using h
  have hprev := st128_p232
  have hstep := st128_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p234 : ((16452770745543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT128 (i+1))
      = (∑ i ∈ Finset.range 233, stT128 (i+1)) + stT128 234 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 233
    simpa using h
  have hprev := st128_p233
  have hstep := st128_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p235 : ((8193310661649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT128 (i+1))
      = (∑ i ∈ Finset.range 234, stT128 (i+1)) + stT128 235 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 234
    simpa using h
  have hprev := st128_p234
  have hstep := st128_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p236 : ((15995212651413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT128 (i+1))
      = (∑ i ∈ Finset.range 235, stT128 (i+1)) + stT128 236 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 235
    simpa using h
  have hprev := st128_p235
  have hstep := st128_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p237 : ((15393042423883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT128 (i+1))
      = (∑ i ∈ Finset.range 236, stT128 (i+1)) + stT128 237 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 236
    simpa using h
  have hprev := st128_p236
  have hstep := st128_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p238 : ((14752519641283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT128 (i+1))
      = (∑ i ∈ Finset.range 237, stT128 (i+1)) + stT128 238 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 237
    simpa using h
  have hprev := st128_p237
  have hstep := st128_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p239 : ((3563517261447/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT128 (i+1))
      = (∑ i ∈ Finset.range 238, stT128 (i+1)) + stT128 239 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 238
    simpa using h
  have hprev := st128_p238
  have hstep := st128_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p240 : ((877224531357/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT128 (i+1))
      = (∑ i ∈ Finset.range 239, stT128 (i+1)) + stT128 240 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 239
    simpa using h
  have hprev := st128_p239
  have hstep := st128_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p241 : ((353882851189/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT128 (i+1))
      = (∑ i ∈ Finset.range 240, stT128 (i+1)) + stT128 241 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 240
    simpa using h
  have hprev := st128_p240
  have hstep := st128_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p242 : ((364442681743/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT128 (i+1))
      = (∑ i ∈ Finset.range 241, stT128 (i+1)) + stT128 242 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 241
    simpa using h
  have hprev := st128_p241
  have hstep := st128_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p243 : ((759269978911/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT128 (i+1))
      = (∑ i ∈ Finset.range 242, stT128 (i+1)) + stT128 243 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 242
    simpa using h
  have hprev := st128_p242
  have hstep := st128_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p244 : ((3953206337821/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT128 (i+1))
      = (∑ i ∈ Finset.range 243, stT128 (i+1)) + stT128 244 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 243
    simpa using h
  have hprev := st128_p243
  have hstep := st128_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p245 : ((162917370229/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT128 (i+1))
      = (∑ i ∈ Finset.range 244, stT128 (i+1)) + stT128 245 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 244
    simpa using h
  have hprev := st128_p244
  have hstep := st128_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p246 : ((4123998673929/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT128 (i+1))
      = (∑ i ∈ Finset.range 245, stT128 (i+1)) + stT128 246 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 245
    simpa using h
  have hprev := st128_p245
  have hstep := st128_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p247 : ((8186928622413/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT128 (i+1))
      = (∑ i ∈ Finset.range 246, stT128 (i+1)) + stT128 247 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 246
    simpa using h
  have hprev := st128_p246
  have hstep := st128_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p248 : ((3191955761547/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT128 (i+1))
      = (∑ i ∈ Finset.range 247, stT128 (i+1)) + stT128 248 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 247
    simpa using h
  have hprev := st128_p247
  have hstep := st128_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p249 : ((1536345815841/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT128 (i+1))
      = (∑ i ∈ Finset.range 248, stT128 (i+1)) + stT128 249 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 248
    simpa using h
  have hprev := st128_p248
  have hstep := st128_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_p250 : ((7369916254541/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT128 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT128 (i+1))
      = (∑ i ∈ Finset.range 249, stT128 (i+1)) + stT128 250 := by
    have h := Finset.sum_range_succ (fun i => stT128 (i+1)) 249
    simpa using h
  have hprev := st128_p249
  have hstep := st128_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st128_s250 :
    |Real.sin (((128 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))
      - ((-33363/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -1486997/2000000) (δ := 6513/1000000000) (ψ := -8717/31250) 128 113
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 128`** (evaluated boundary). -/
theorem station_128_sign : hardyG ((((128:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 128 250 (by norm_num) (by norm_num)
    ((-8717/31250 : ℚ) : ℝ)
  have hchain := st128_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT128 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((128 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-8717/31250 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st128_c250
  have hsinb := abs_le.mp st128_s250
  have hbdy_lo : ((2762422908499/131074000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((128 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-8717/31250 : ℚ) : ℝ))) / 2
          - ((((128:ℕ)):ℝ))
            * Real.sin (((128 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-8717/31250 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((128:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((128:ℝ) * Real.log (250:ℝ) - ((-8717/31250 : ℚ) : ℝ))) / 2
        - ((128:ℝ)) * Real.sin ((128:ℝ) * Real.log (250:ℝ) - ((-8717/31250 : ℚ) : ℝ))
        ≥ ((21838889/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((128:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((21838889/1000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((21838889/1000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((21838889/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((128:ℕ)):ℝ))+1) * (((((128:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((24205435089/62500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((7369916254541/5000000000000 : ℚ) : ℝ) + ((2762422908499/131074000000000 : ℚ) : ℝ)
      - ((24205435089/62500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-8717/31250 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((128:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-8717/31250 : ℚ) : ℝ)
        * (riemannZeta (line ((((128:ℕ)):ℝ)))).re
      - Real.sin ((-8717/31250 : ℚ) : ℝ)
        * (riemannZeta (line ((((128:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((128:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((128:ℕ)):ℝ))
      = (((((128:ℕ)):ℝ)) * (Real.log ((((128:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((128:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_128
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
  have hθwin : |(((-8717/31250 : ℚ) : ℝ) + ((21:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((128:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((128:ℕ)):ℝ)))
    (φ := ((-8717/31250 : ℚ) : ℝ) + ((21:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-8717/31250 : ℚ) : ℝ) + ((21:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-8717/31250 : ℚ)) : ℝ) - Real.pi) + ((21:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-8717/31250 : ℚ)) : ℝ) - Real.pi) 21).1,
    (cos_sin_shift ((((-8717/31250 : ℚ)) : ℝ) - Real.pi) 21).2]
  exact cos_sin_flip ((-8717/31250 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_128_sign
end AxiomAudit
