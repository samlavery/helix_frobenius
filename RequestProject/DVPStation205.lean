import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 205` (rung-217.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT205 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((205 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))

theorem st205_c1 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((992527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 76457/2500000) (δ := 201/1000000000) (ψ := -122331/1000000) 205 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t1 : ((992477/1000000 : ℚ) : ℝ) ≤ stT205 1 := by
  have hc : ((992477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((992477/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((992477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c2 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-82889/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5739413/10000000) (δ := 10367/1000000000) (ψ := -122331/1000000) 205 23
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t2 : ((-586157949627/1250000000000 : ℚ) : ℝ) ≤ stT205 2 := by
  have hc : ((-331581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-586157949627/1250000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-331581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c3 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((654837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -267759/1250000) (δ := 513/50000000) (ψ := -122331/1000000) 205 36
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t3 : ((1890207027037/5000000000000 : ℚ) : ℝ) ≤ stT205 3 := by
  have hc : ((654787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1890207027037/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((654787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c4 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 784667/2000000) (δ := 413/40000000) (ψ := -122331/1000000) 205 45
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t4 : ((353/500000 : ℚ) : ℝ) ≤ stT205 4 := by
  have hc : ((353/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((353/500000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((353/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c5 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-491013/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1844819/2500000) (δ := 5191/500000000) (ψ := -122331/1000000) 205 53
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t5 : ((-137249294823/312500000000 : ℚ) : ℝ) ≤ stT205 5 := by
  have hc : ((-245519/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137249294823/312500000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-245519/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c6 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-495563/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1880169/2500000) (δ := 2057/200000000) (ψ := -122331/1000000) 205 58
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t6 : ((-505807396251/1250000000000 : ℚ) : ℝ) ≤ stT205 6 := by
  have hc : ((-123897/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-505807396251/1250000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-123897/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c7 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-998667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -772487/1000000) (δ := 5171/500000000) (ψ := -122331/1000000) 205 64
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t7 : ((-754959143093/2000000000000 : ℚ) : ℝ) ≤ stT205 7 := by
  have hc : ((-998717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-754959143093/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-998717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c8 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((16523/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53047/250000) (δ := 1039/100000000) (ψ := -122331/1000000) 205 68
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t8 : ((233652769371/1000000000000 : ℚ) : ℝ) ≤ stT205 8 := by
  have hc : ((66087/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233652769371/1000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((66087/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c9 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-52417/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2294973/5000000) (δ := 2057/200000000) (ψ := -122331/1000000) 205 72
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t9 : ((-87378350809/1000000000000 : ℚ) : ℝ) ≤ stT205 9 := by
  have hc : ((-52427/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87378350809/1000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-52427/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c10 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((611083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2283421/10000000) (δ := 261/25000000) (ψ := -122331/1000000) 205 75
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t10 : ((1932255602141/10000000000000 : ℚ) : ℝ) ≤ stT205 10 := by
  have hc : ((611033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1932255602141/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((611033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c11 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-15801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 500751/1250000) (δ := 10341/1000000000) (ψ := -122331/1000000) 205 78
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t11 : ((-11929298541/1250000000000 : ℚ) : ℝ) ≤ stT205 11 := by
  have hc : ((-7913/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11929298541/1250000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-7913/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c12 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((415419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1475461/10000000) (δ := 10283/1000000000) (ψ := -122331/1000000) 205 81
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t12 : ((599569522447/2500000000000 : ℚ) : ℝ) ≤ stT205 12 := by
  have hc : ((207697/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((599569522447/2500000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((207697/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c13 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-34523/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -925309/2000000) (δ := 2061/200000000) (ψ := -122331/1000000) 205 84
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t13 : ((-383067637617/5000000000000 : ℚ) : ℝ) ≤ stT205 13 := by
  have hc : ((-138117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-383067637617/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-138117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c14 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((142863/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 968939/5000000) (δ := 649/62500000) (ψ := -122331/1000000) 205 86
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t14 : ((95447660509/500000000000 : ℚ) : ℝ) ≤ stT205 14 := by
  have hc : ((142853/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95447660509/500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((142853/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c15 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-140873/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5880813/10000000) (δ := 1027/100000000) (ψ := -122331/1000000) 205 88
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t15 : ((-363758356287/2000000000000 : ℚ) : ℝ) ≤ stT205 15 := by
  have hc : ((-140883/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-363758356287/2000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-140883/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c16 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-992167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1885217/2500000) (δ := 2587/250000000) (ψ := -122331/1000000) 205 90
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t16 : ((-2480543492217/10000000000000 : ℚ) : ℝ) ≤ stT205 16 := by
  have hc : ((-992217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2480543492217/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-992217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c17 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-193093/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7195049/10000000) (δ := 5181/500000000) (ψ := -122331/1000000) 205 92
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t17 : ((-468343712771/2000000000000 : ℚ) : ℝ) ≤ stT205 17 := by
  have hc : ((-193103/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-468343712771/2000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-193103/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c18 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-221223/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2536401/5000000) (δ := 10327/1000000000) (ψ := -122331/1000000) 205 94
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t18 : ((-8148228511/78125000000 : ℚ) : ℝ) ≤ stT205 18 := by
  have hc : ((-6914/15625 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8148228511/78125000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-6914/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c19 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((170867/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 341579/2500000) (δ := 10391/1000000000) (ψ := -122331/1000000) 205 96
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t19 : ((391972782549/2000000000000 : ℚ) : ℝ) ≤ stT205 19 := by
  have hc : ((170857/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((391972782549/2000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((170857/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c20 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((6603/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -752359/2000000) (δ := 5199/500000000) (ψ := -122331/1000000) 205 98
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t20 : ((7376785033/500000000000 : ℚ) : ℝ) ≤ stT205 20 := by
  have hc : ((3299/50000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7376785033/500000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((3299/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c21 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-74979/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 276761/500000) (δ := 2603/250000000) (ψ := -122331/1000000) 205 99
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t21 : ((-654524951439/5000000000000 : ℚ) : ℝ) ≤ stT205 21 := by
  have hc : ((-299941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-654524951439/5000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-299941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c22 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((685371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2039207/10000000) (δ := 2569/250000000) (ψ := -122331/1000000) 205 101
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t22 : ((1461109169247/10000000000000 : ℚ) : ℝ) ≤ stT205 22 := by
  have hc : ((685321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1461109169247/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((685321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c23 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-428611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5034377/10000000) (δ := 10369/1000000000) (ψ := -122331/1000000) 205 102
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t23 : ((-178764068169/2000000000000 : ℚ) : ℝ) ≤ stT205 23 := by
  have hc : ((-428661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178764068169/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-428661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c24 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-127141/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2284877/5000000) (δ := 2587/250000000) (ψ := -122331/1000000) 205 104
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t24 : ((-64894145043/1250000000000 : ℚ) : ℝ) ≤ stT205 24 := by
  have hc : ((-63583/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64894145043/1250000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-63583/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c25 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((967049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 643557/10000000) (δ := 653/62500000) (ψ := -122331/1000000) 205 105
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t25 : ((966999/5000000 : ℚ) : ℝ) ≤ stT205 25 := by
  have hc : ((966999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((966999/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((966999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c26 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-42927/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5036203/10000000) (δ := 10263/1000000000) (ψ := -122331/1000000) 205 106
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t26 : ((-10524575873/125000000000 : ℚ) : ℝ) ≤ stT205 26 := by
  have hc : ((-10733/25000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10524575873/125000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-10733/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c27 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-473591/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -351891/500000) (δ := 5163/500000000) (ψ := -122331/1000000) 205 108
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t27 : ((-56967154101/312500000000 : ℚ) : ℝ) ≤ stT205 27 := by
  have hc : ((-29601/31250 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56967154101/312500000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-29601/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c28 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-18019/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4107337/10000000) (δ := 10319/1000000000) (ψ := -122331/1000000) 205 109
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t28 : ((-68152686849/5000000000000 : ℚ) : ℝ) ≤ stT205 28 := by
  have hc : ((-36063/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68152686849/5000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-36063/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c29 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((743569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1831009/10000000) (δ := 1289/125000000) (ψ := -122331/1000000) 205 110
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t29 : ((1380679837607/10000000000000 : ℚ) : ℝ) ≤ stT205 29 := by
  have hc : ((743519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1380679837607/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((743519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c30 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((997837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -164453/10000000) (δ := 5199/500000000) (ψ := -122331/1000000) 205 111
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t30 : ((1821700635167/10000000000000 : ℚ) : ℝ) ≤ stT205 30 := by
  have hc : ((997787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1821700635167/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((997787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c31 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((232813/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 932407/10000000) (δ := 10297/1000000000) (ψ := -122331/1000000) 205 112
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t31 : ((836244072853/5000000000000 : ℚ) : ℝ) ≤ stT205 31 := by
  have hc : ((465601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((836244072853/5000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((465601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c32 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((206579/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1495653/10000000) (δ := 10413/1000000000) (ψ := -122331/1000000) 205 113
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t32 : ((365161235439/2500000000000 : ℚ) : ℝ) ≤ stT205 32 := by
  have hc : ((413133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((365161235439/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((413133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c33 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((50749/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 779067/5000000) (δ := 10383/1000000000) (ψ := -122331/1000000) 205 114
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t33 : ((88337201299/625000000000 : ℚ) : ℝ) ≤ stT205 33 := by
  have hc : ((405967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88337201299/625000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((405967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c34 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((448041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 574917/5000000) (δ := 10427/1000000000) (ψ := -122331/1000000) 205 115
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t34 : ((9604258997/62500000000 : ℚ) : ℝ) ≤ stT205 34 := by
  have hc : ((28001/31250 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9604258997/62500000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((28001/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c35 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((496453/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 74491/2500000) (δ := 10269/1000000000) (ψ := -122331/1000000) 205 116
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t35 : ((52444763739/312500000000 : ℚ) : ℝ) ≤ stT205 35 := by
  have hc : ((124107/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52444763739/312500000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((124107/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c36 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((462651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -972413/10000000) (δ := 10261/1000000000) (ψ := -122331/1000000) 205 117
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t36 : ((192760756229/1250000000000 : ℚ) : ℝ) ≤ stT205 36 := by
  have hc : ((231313/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192760756229/1250000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((231313/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c37 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((246459/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2638389/10000000) (δ := 5177/500000000) (ψ := -122331/1000000) 205 118
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t37 : ((202567392613/2500000000000 : ℚ) : ℝ) ≤ stT205 37 := by
  have hc : ((123217/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202567392613/2500000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((123217/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c38 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-237/800 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46789/100000) (δ := 10447/1000000000) (ψ := -122331/1000000) 205 119
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t38 : ((-961324609/20000000000 : ℚ) : ℝ) ≤ stT205 38 := by
  have hc : ((-2963/10000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-961324609/20000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-2963/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c39 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-38071/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7074419/10000000) (δ := 10263/1000000000) (ψ := -122331/1000000) 205 120
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t39 : ((-30482804793/200000000000 : ℚ) : ℝ) ≤ stT205 39 := by
  have hc : ((-38073/40000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30482804793/200000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-38073/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c40 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-710061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5900953/10000000) (δ := 261/25000000) (ψ := -122331/1000000) 205 120
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t40 : ((-1122784196429/10000000000000 : ℚ) : ℝ) ≤ stT205 40 := by
  have hc : ((-710111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1122784196429/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-710111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c41 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((20917/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 711987/2500000) (δ := 1037/100000000) (ψ := -122331/1000000) 205 121
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t41 : ((65325896973/1000000000000 : ℚ) : ℝ) ≤ stT205 41 := by
  have hc : ((41829/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65325896973/1000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((41829/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c42 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((15301/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -127499/2500000) (δ := 5213/500000000) (ψ := -122331/1000000) 205 122
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t42 : ((755479758031/5000000000000 : ℚ) : ℝ) ≤ stT205 42 := by
  have hc : ((489607/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((755479758031/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((489607/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c43 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-46251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2079289/5000000) (δ := 5209/500000000) (ψ := -122331/1000000) 205 123
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t43 : ((-8821281517/625000000000 : ℚ) : ℝ) ≤ stT205 43 := by
  have hc : ((-11569/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8821281517/625000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-11569/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c44 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-199151/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7623541/10000000) (δ := 5159/500000000) (ψ := -122331/1000000) 205 123
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t44 : ((-300246559677/2000000000000 : ℚ) : ℝ) ≤ stT205 44 := by
  have hc : ((-199161/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-300246559677/2000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-199161/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c45 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((196357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 429111/1250000) (δ := 2573/250000000) (ψ := -122331/1000000) 205 124
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t45 : ((292637004277/10000000000000 : ℚ) : ℝ) ≤ stT205 45 := by
  have hc : ((196307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((292637004277/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((196307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c46 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((229839/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1010889/10000000) (δ := 10299/1000000000) (ψ := -122331/1000000) 205 125
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t46 : ((677721116607/5000000000000 : ℚ) : ℝ) ≤ stT205 46 := by
  have hc : ((459653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((677721116607/5000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((459653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c47 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-16257/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2848437/5000000) (δ := 10397/1000000000) (ψ := -122331/1000000) 205 126
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t47 : ((-1897207709/20000000000 : ℚ) : ℝ) ≤ stT205 47 := by
  have hc : ((-65033/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1897207709/20000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-65033/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c48 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-17987/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2546497/5000000) (δ := 5153/500000000) (ψ := -122331/1000000) 205 126
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t48 : ((-1622805679/25000000000 : ℚ) : ℝ) ≤ stT205 48 := by
  have hc : ((-17989/40000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1622805679/25000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-17989/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c49 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((999819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47629/10000000) (δ := 10413/1000000000) (ψ := -122331/1000000) 205 127
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t49 : ((1428241000099/10000000000000 : ℚ) : ℝ) ≤ stT205 49 := by
  have hc : ((999769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1428241000099/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((999769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c50 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-89/160 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2700829/5000000) (δ := 10383/1000000000) (ψ := -122331/1000000) 205 128
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t50 : ((-3933636241/50000000000 : ℚ) : ℝ) ≤ stT205 50 := by
  have hc : ((-5563/10000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3933636241/50000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-5563/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c51 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-16111/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 189887/400000) (δ := 129/12500000) (ψ := -122331/1000000) 205 128
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t51 : ((-45126855787/1000000000000 : ℚ) : ℝ) ≤ stT205 51 := by
  have hc : ((-32227/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45126855787/1000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-32227/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c52 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((919651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -252253/2500000) (δ := 1291/125000000) (ψ := -122331/1000000) 205 129
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t52 : ((5101026747/40000000000 : ℚ) : ℝ) ≤ stT205 52 := by
  have hc : ((919601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5101026747/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((919601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c53 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-117001/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6954773/10000000) (δ := 2567/250000000) (ψ := -122331/1000000) 205 130
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t53 : ((-321443721287/2500000000000 : ℚ) : ℝ) ≤ stT205 53 := by
  have hc : ((-468029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-321443721287/2500000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-468029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c54 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((124399/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 82029/312500) (δ := 81/7812500) (ψ := -122331/1000000) 205 130
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t54 : ((338537015271/5000000000000 : ℚ) : ℝ) ≤ stT205 54 := by
  have hc : ((248773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((338537015271/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((248773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c55 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((49493/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3679121/10000000) (δ := 5171/500000000) (ψ := -122331/1000000) 205 131
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t55 : ((16675650433/1250000000000 : ℚ) : ℝ) ≤ stT205 55 := by
  have hc : ((12367/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16675650433/1250000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((12367/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c56 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-606259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 34721/62500) (δ := 10261/1000000000) (ψ := -122331/1000000) 205 131
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t56 : ((-810214960863/10000000000000 : ℚ) : ℝ) ≤ stT205 56 := by
  have hc : ((-606309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-810214960863/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-606309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c57 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((907869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -540779/5000000) (δ := 10349/1000000000) (ψ := -122331/1000000) 205 132
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t57 : ((300608828927/2500000000000 : ℚ) : ℝ) ≤ stT205 57 := by
  have hc : ((907819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((300608828927/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((907819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c58 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-24999/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7831739/10000000) (δ := 5177/500000000) (ψ := -122331/1000000) 205 132
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t58 : ((-26261562613/200000000000 : ℚ) : ℝ) ≤ stT205 58 := by
  have hc : ((-100001/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26261562613/200000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-100001/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c59 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((938041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55291/625000) (δ := 641/62500000) (ψ := -122331/1000000) 205 133
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t59 : ((1221160164999/10000000000000 : ℚ) : ℝ) ≤ stT205 59 := by
  have hc : ((937991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1221160164999/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((937991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c60 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-158277/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6209669/10000000) (δ := 10439/1000000000) (ψ := -122331/1000000) 205 134
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t60 : ((-40869545113/400000000000 : ℚ) : ℝ) ≤ stT205 60 := by
  have hc : ((-158287/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40869545113/400000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-158287/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c61 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((617969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1130799/5000000) (δ := 2591/250000000) (ψ := -122331/1000000) 205 134
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t61 : ((49447732137/625000000000 : ℚ) : ℝ) ≤ stT205 61 := by
  have hc : ((617919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49447732137/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((617919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c62 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-228379/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5112859/10000000) (δ := 10371/1000000000) (ψ := -122331/1000000) 205 135
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t62 : ((-36259192101/625000000000 : ℚ) : ℝ) ≤ stT205 62 := by
  have hc : ((-57101/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36259192101/625000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-57101/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c63 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((329579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1543673/5000000) (δ := 10371/1000000000) (ψ := -122331/1000000) 205 135
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t63 : ((415167326049/10000000000000 : ℚ) : ℝ) ≤ stT205 63 := by
  have hc : ((329529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((415167326049/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((329529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c64 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-246483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2274807/5000000) (δ := 413/40000000) (ψ := -122331/1000000) 205 136
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t64 : ((-308166496533/10000000000000 : ℚ) : ℝ) ≤ stT205 64 := by
  have hc : ((-246533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-308166496533/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-246533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c65 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((21069/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3396289/10000000) (δ := 5189/500000000) (ψ := -122331/1000000) 205 136
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t65 : ((3265833651/125000000000 : ℚ) : ℝ) ≤ stT205 65 := by
  have hc : ((2633/12500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3265833651/125000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((2633/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c66 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-222167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4487081/10000000) (δ := 5159/500000000) (ψ := -122331/1000000) 205 137
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t66 : ((-54706047711/2000000000000 : ℚ) : ℝ) ≤ stT205 66 := by
  have hc : ((-222217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54706047711/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-222217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c67 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((139551/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3219843/10000000) (δ := 2057/200000000) (ψ := -122331/1000000) 205 137
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t67 : ((42614519261/1250000000000 : ℚ) : ℝ) ≤ stT205 67 := by
  have hc : ((69763/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42614519261/1250000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((69763/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c68 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-188871/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2447691/5000000) (δ := 10411/1000000000) (ψ := -122331/1000000) 205 138
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t68 : ((-7158444137/156250000000 : ℚ) : ℝ) ≤ stT205 68 := by
  have hc : ((-5903/15625 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7158444137/156250000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-5903/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c69 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((510869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2586503/10000000) (δ := 10411/1000000000) (ψ := -122331/1000000) 205 138
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t69 : ((307476769851/5000000000000 : ℚ) : ℝ) ≤ stT205 69 := by
  have hc : ((510819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((307476769851/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((510819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c70 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-41591/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5747251/10000000) (δ := 10299/1000000000) (ψ := -122331/1000000) 205 139
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t70 : ((-397716035437/5000000000000 : ℚ) : ℝ) ≤ stT205 70 := by
  have hc : ((-332753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-397716035437/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-332753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c71 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((820253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 380589/2500000) (δ := 2601/250000000) (ψ := -122331/1000000) 205 139
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t71 : ((973401336543/10000000000000 : ℚ) : ℝ) ≤ stT205 71 := by
  have hc : ((820203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((973401336543/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((820203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c72 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-944561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1754407/2500000) (δ := 10307/1000000000) (ψ := -122331/1000000) 205 140
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t72 : ((-69577212427/625000000000 : ℚ) : ℝ) ≤ stT205 72 := by
  have hc : ((-944611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69577212427/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-944611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c73 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((249947/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 25719/5000000) (δ := 1287/125000000) (ψ := -122331/1000000) 205 140
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t73 : ((585052176159/5000000000000 : ℚ) : ℝ) ≤ stT205 73 := by
  have hc : ((499869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((585052176159/5000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((499869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c74 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-189087/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1756077/2500000) (δ := 1287/125000000) (ψ := -122331/1000000) 205 140
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t74 : ((-219820913269/2000000000000 : ℚ) : ℝ) ≤ stT205 74 := by
  have hc : ((-189097/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219820913269/2000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-189097/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c75 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((375333/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -451079/2500000) (δ := 5207/500000000) (ψ := -122331/1000000) 205 141
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t75 : ((1083420369/12500000000 : ℚ) : ℝ) ≤ stT205 75 := by
  have hc : ((93827/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1083420369/12500000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((93827/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c76 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-51283/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4983849/10000000) (δ := 5207/500000000) (ψ := -122331/1000000) 205 141
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t76 : ((-235331286403/5000000000000 : ℚ) : ℝ) ≤ stT205 76 := by
  have hc : ((-205157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-235331286403/5000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-205157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c77 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-39059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4024663/10000000) (δ := 10421/1000000000) (ψ := -122331/1000000) 205 142
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t77 : ((-22284425527/5000000000000 : ℚ) : ℝ) ≤ stT205 77 := by
  have hc : ((-39109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22284425527/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-39109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c78 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((510241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2588329/10000000) (δ := 5141/500000000) (ψ := -122331/1000000) 205 142
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t78 : ((577677534907/10000000000000 : ℚ) : ℝ) ≤ stT205 78 := by
  have hc : ((510191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((577677534907/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((510191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c79 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-875061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6590897/10000000) (δ := 83/8000000) (ψ := -122331/1000000) 205 143
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t79 : ((-30768027649/312500000000 : ℚ) : ℝ) ≤ stT205 79 := by
  have hc : ((-875111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30768027649/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-875111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c80 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((15599/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72131/5000000) (δ := 83/8000000) (ψ := -122331/1000000) 205 143
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t80 : ((558058345719/5000000000000 : ℚ) : ℝ) ≤ stT205 80 := by
  have hc : ((499143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((558058345719/5000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((499143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c81 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-99307/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 622227/1000000) (δ := 2607/250000000) (ψ := -122331/1000000) 205 143
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t81 : ((-55174071917/625000000000 : ℚ) : ℝ) ≤ stT205 81 := by
  have hc : ((-397253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55174071917/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-397253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c82 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((143881/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3197267/10000000) (δ := 2087/200000000) (ψ := -122331/1000000) 205 144
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t82 : ((1985779233/62500000000 : ℚ) : ℝ) ≤ stT205 82 := by
  have hc : ((8991/31250 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1985779233/62500000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((8991/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c83 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((178389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60299/200000) (δ := 2567/250000000) (ψ := -122331/1000000) 205 144
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t83 : ((24472477211/625000000000 : ℚ) : ℝ) ≤ stT205 83 := by
  have hc : ((44591/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24472477211/625000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((44591/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c84 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-217017/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1638809/2500000) (δ := 20643/1000000000) (ψ := -122331/1000000) 205 145
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t84 : ((-47359743431/500000000000 : ℚ) : ℝ) ≤ stT205 84 := by
  have hc : ((-434059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47359743431/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-434059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c85 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((980847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -490081/10000000) (δ := 259/25000000) (ψ := -122331/1000000) 205 145
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t85 : ((265955856911/2500000000000 : ℚ) : ℝ) ≤ stT205 85 := by
  have hc : ((980797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((265955856911/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((980797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c86 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-73729/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5504119/10000000) (δ := 259/25000000) (ψ := -122331/1000000) 205 145
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t86 : ((-39755392331/625000000000 : ℚ) : ℝ) ≤ stT205 86 := by
  have hc : ((-294941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39755392331/625000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-294941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c87 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-140293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4278883/10000000) (δ := 10353/1000000000) (ψ := -122331/1000000) 205 146
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t87 : ((-150463554759/10000000000000 : ℚ) : ℝ) ≤ stT205 87 := by
  have hc : ((-140343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-150463554759/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-140343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c88 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((807243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 789163/5000000) (δ := 10253/1000000000) (ψ := -122331/1000000) 205 146
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t88 : ((860470159579/10000000000000 : ℚ) : ℝ) ≤ stT205 88 := by
  have hc : ((807193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((860470159579/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((807193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c89 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-981267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 184233/250000) (δ := 207/20000000) (ψ := -122331/1000000) 205 146
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t89 : ((-520097028683/5000000000000 : ℚ) : ℝ) ≤ stT205 89 := by
  have hc : ((-981317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-520097028683/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-981317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c90 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((250981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2612327/10000000) (δ := 10357/1000000000) (ψ := -122331/1000000) 205 147
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t90 : ((16533169497/312500000000 : ℚ) : ℝ) ≤ stT205 90 := by
  have hc : ((62739/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16533169497/312500000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((62739/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c91 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((2747/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3050721/10000000) (δ := 20557/1000000000) (ψ := -122331/1000000) 205 147
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t91 : ((3599021043/100000000000 : ℚ) : ℝ) ≤ stT205 91 := by
  have hc : ((13733/40000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3599021043/100000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((13733/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c92 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-474751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -882013/1250000) (δ := 2591/250000000) (ψ := -122331/1000000) 205 148
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t92 : ((-61873579831/625000000000 : ℚ) : ℝ) ≤ stT205 92 := by
  have hc : ((-59347/62500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61873579831/625000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-59347/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c93 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((164363/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -757759/5000000) (δ := 1283/125000000) (ψ := -122331/1000000) 205 148
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t93 : ((170426007703/2000000000000 : ℚ) : ℝ) ≤ stT205 93 := by
  have hc : ((164353/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170426007703/2000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((164353/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c94 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-3883/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3965823/10000000) (δ := 10339/1000000000) (ψ := -122331/1000000) 205 148
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t94 : ((-4017904401/2500000000000 : ℚ) : ℝ) ≤ stT205 94 := by
  have hc : ((-7791/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4017904401/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-7791/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c95 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-817311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3159407/5000000) (δ := 2583/250000000) (ψ := -122331/1000000) 205 149
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t95 : ((-838595221419/10000000000000 : ℚ) : ℝ) ≤ stT205 95 := by
  have hc : ((-817361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-838595221419/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-817361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c96 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((928327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -952273/10000000) (δ := 163/15625000) (ψ := -122331/1000000) 205 149
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t96 : ((47370903587/500000000000 : ℚ) : ℝ) ≤ stT205 96 := by
  have hc : ((928277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47370903587/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((928277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c97 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-42953/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2179331/5000000) (δ := 163/15625000) (ψ := -122331/1000000) 205 149
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t97 : ((-87249783057/5000000000000 : ℚ) : ℝ) ≤ stT205 97 := by
  have hc : ((-85931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87249783057/5000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-85931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c98 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-152393/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1218569/2000000) (δ := 417/40000000) (ψ := -122331/1000000) 205 150
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t98 : ((-153950347659/2000000000000 : ℚ) : ℝ) ≤ stT205 98 := by
  have hc : ((-152403/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153950347659/2000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-152403/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c99 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((187467/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -44487/500000) (δ := 417/40000000) (ψ := -122331/1000000) 205 150
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t99 : ((188401220909/2000000000000 : ℚ) : ℝ) ≤ stT205 99 := by
  have hc : ((187457/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188401220909/2000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((187457/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c100 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-66611/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4261039/10000000) (δ := 413/40000000) (ψ := -122331/1000000) 205 150
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t100 : ((-16659/1250000 : ℚ) : ℝ) ≤ stT205 100 := by
  have hc : ((-16659/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16659/1250000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-16659/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c101 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-411917/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -396709/625000) (δ := 5143/500000000) (ψ := -122331/1000000) 205 151
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t101 : ((-102474485949/1250000000000 : ℚ) : ℝ) ≤ stT205 101 := by
  have hc : ((-205971/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102474485949/1250000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-205971/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c102 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((54263/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32451/250000) (δ := 5193/500000000) (ψ := -122331/1000000) 205 151
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t102 : ((429802019613/5000000000000 : ℚ) : ℝ) ≤ stT205 102 := by
  have hc : ((434079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((429802019613/5000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((434079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c103 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((8989/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3701961/10000000) (δ := 5143/500000000) (ψ := -122331/1000000) 205 151
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t103 : ((1106524467/125000000000 : ℚ) : ℝ) ≤ stT205 103 := by
  have hc : ((1123/12500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1106524467/125000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((1123/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c104 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-949273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7054279/10000000) (δ := 1041/100000000) (ψ := -122331/1000000) 205 152
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t104 : ((-930888096663/10000000000000 : ℚ) : ℝ) ≤ stT205 104 := by
  have hc : ((-949323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-930888096663/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-949323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c105 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((130493/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -214991/1000000) (δ := 1031/100000000) (ψ := -122331/1000000) 205 152
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t105 : ((1273383597/20000000000 : ℚ) : ℝ) ≤ stT205 105 := by
  have hc : ((130483/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1273383597/20000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((130483/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c106 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((468531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 676981/2500000) (δ := 10293/1000000000) (ψ := -122331/1000000) 205 152
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t106 : ((91005713617/2000000000000 : ℚ) : ℝ) ≤ stT205 106 := by
  have hc : ((468481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91005713617/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((468481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c107 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-9911/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1880049/2500000) (δ := 1041/100000000) (ψ := -122331/1000000) 205 152
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t107 : ((-19163627551/200000000000 : ℚ) : ℝ) ≤ stT205 107 := by
  have hc : ((-19823/20000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19163627551/200000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-19823/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c108 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((201297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3420287/10000000) (δ := 10303/1000000000) (ψ := -122331/1000000) 205 153
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t108 : ((774599703/40000000000 : ℚ) : ℝ) ≤ stT205 108 := by
  have hc : ((201247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((774599703/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((201247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c109 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((433589/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1303221/10000000) (δ := 13/1250000) (ψ := -122331/1000000) 205 153
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t109 : ((51909858983/625000000000 : ℚ) : ℝ) ≤ stT205 109 := by
  have hc : ((108391/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51909858983/625000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((108391/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c110 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-366477/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5983627/10000000) (δ := 103/10000000) (ψ := -122331/1000000) 205 153
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t110 : ((-174723048213/2500000000000 : ℚ) : ℝ) ≤ stT205 110 := by
  have hc : ((-183251/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174723048213/2500000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-183251/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c111 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-111817/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5086263/10000000) (δ := 2599/250000000) (ψ := -122331/1000000) 205 154
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t111 : ((-106143864561/2500000000000 : ℚ) : ℝ) ≤ stT205 111 := by
  have hc : ((-223659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106143864561/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-223659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c112 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((196173/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -97971/2000000) (δ := 10307/1000000000) (ψ := -122331/1000000) 205 154
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t112 : ((185356576493/2000000000000 : ℚ) : ℝ) ≤ stT205 112 := by
  have hc : ((196163/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185356576493/2000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((196163/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c113 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-27739/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4065757/10000000) (δ := 2599/250000000) (ψ := -122331/1000000) 205 154
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t113 : ((-6529544461/1250000000000 : ℚ) : ℝ) ≤ stT205 113 := by
  have hc : ((-6941/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6529544461/1250000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-6941/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c114 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-957991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7126773/10000000) (δ := 5207/500000000) (ψ := -122331/1000000) 205 155
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t114 : ((-448643894013/5000000000000 : ℚ) : ℝ) ≤ stT205 114 := by
  have hc : ((-958041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-448643894013/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-958041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c115 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((48861/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20709/78125) (δ := 5157/500000000) (ψ := -122331/1000000) 205 155
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t115 : ((711850241/15625000000 : ℚ) : ℝ) ≤ stT205 115 := by
  have hc : ((6107/12500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((711850241/15625000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((6107/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c116 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((755363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1786473/10000000) (δ := 5157/500000000) (ψ := -122331/1000000) 205 155
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t116 : ((175322498247/2500000000000 : ℚ) : ℝ) ≤ stT205 116 := by
  have hc : ((755313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175322498247/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((755313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c117 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-19637/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 618567/1000000) (δ := 10389/1000000000) (ψ := -122331/1000000) 205 155
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t117 : ((-72622327053/1000000000000 : ℚ) : ℝ) ≤ stT205 117 := by
  have hc : ((-78553/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72622327053/1000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-78553/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c118 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-473647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5160559/10000000) (δ := 5161/500000000) (ψ := -122331/1000000) 205 156
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t118 : ((-17442944631/400000000000 : ℚ) : ℝ) ≤ stT205 118 := by
  have hc : ((-473697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17442944631/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-473697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c119 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((18893/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -417837/5000000) (δ := 5161/500000000) (ψ := -122331/1000000) 205 156
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t119 : ((2164782327/25000000000 : ℚ) : ℝ) ≤ stT205 119 := by
  have hc : ((4723/5000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2164782327/25000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((4723/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c120 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((188431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 86327/250000) (δ := 5211/500000000) (ψ := -122331/1000000) 205 156
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t120 : ((17196736347/1000000000000 : ℚ) : ℝ) ≤ stT205 120 := by
  have hc : ((188381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17196736347/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((188381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c121 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-499127/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1541243/2000000) (δ := 5211/500000000) (ψ := -122331/1000000) 205 156
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t121 : ((-28360911927/312500000000 : ℚ) : ℝ) ≤ stT205 121 := by
  have hc : ((-31197/31250 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28360911927/312500000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-31197/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c122 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((28659/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3783617/10000000) (δ := 10429/1000000000) (ψ := -122331/1000000) 205 157
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t122 : ((12961996169/2500000000000 : ℚ) : ℝ) ≤ stT205 122 := by
  have hc : ((14317/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12961996169/2500000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((14317/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c123 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((987223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 200037/5000000) (δ := 10329/1000000000) (ψ := -122331/1000000) 205 157
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t123 : ((890103291737/10000000000000 : ℚ) : ℝ) ≤ stT205 123 := by
  have hc : ((987173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((890103291737/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((987173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c124 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-246589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4549889/10000000) (δ := 10329/1000000000) (ψ := -122331/1000000) 205 157
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t124 : ((-221488481253/10000000000000 : ℚ) : ℝ) ≤ stT205 124 := by
  have hc : ((-246639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221488481253/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-246639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c125 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-473831/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1760393/2500000) (δ := 10267/1000000000) (ψ := -122331/1000000) 205 158
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t125 : ((-413896557/4882812500 : ℚ) : ℝ) ≤ stT205 125 := by
  have hc : ((-14808/15625 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-413896557/4882812500 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-14808/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c126 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((378013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2957869/10000000) (δ := 2609/250000000) (ψ := -122331/1000000) 205 158
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t126 : ((33671589781/1000000000000 : ℚ) : ℝ) ≤ stT205 126 := by
  have hc : ((377963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33671589781/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((377963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c127 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((905857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 546747/5000000) (δ := 10367/1000000000) (ψ := -122331/1000000) 205 158
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t127 : ((200943319073/2500000000000 : ℚ) : ℝ) ≤ stT205 127 := by
  have hc : ((905807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200943319073/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((905807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c128 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-57107/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2556567/5000000) (δ := 10367/1000000000) (ψ := -122331/1000000) 205 158
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t128 : ((-50481487863/1250000000000 : ℚ) : ℝ) ≤ stT205 128 := by
  have hc : ((-228453/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50481487863/1250000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-228453/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c129 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-109757/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6606451/10000000) (δ := 10443/1000000000) (ψ := -122331/1000000) 205 159
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t129 : ((-386564652903/5000000000000 : ℚ) : ℝ) ≤ stT205 129 := by
  have hc : ((-439053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-386564652903/5000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-439053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c130 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((489247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1324463/5000000) (δ := 10443/1000000000) (ψ := -122331/1000000) 205 159
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t130 : ((214527071213/5000000000000 : ℚ) : ℝ) ≤ stT205 130 := by
  have hc : ((489197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((214527071213/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((489197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c131 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((872097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 127831/1000000) (δ := 10343/1000000000) (ψ := -122331/1000000) 205 159
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t131 : ((95238869011/1250000000000 : ℚ) : ℝ) ≤ stT205 131 := by
  have hc : ((872047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95238869011/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((872047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c132 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-478961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5175667/10000000) (δ := 259/25000000) (ψ := -122331/1000000) 205 159
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t132 : ((-416925905279/10000000000000 : ℚ) : ℝ) ≤ stT205 132 := by
  have hc : ((-479011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-416925905279/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-479011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c133 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-111113/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1666089/2500000) (δ := 10253/1000000000) (ψ := -122331/1000000) 205 160
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t133 : ((-38541045147/500000000000 : ℚ) : ℝ) ≤ stT205 133 := by
  have hc : ((-444477/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38541045147/500000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-444477/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c134 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((106629/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1412699/5000000) (δ := 20553/1000000000) (ψ := -122331/1000000) 205 160
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t134 : ((46051291311/1250000000000 : ℚ) : ℝ) ≤ stT205 134 := by
  have hc : ((213233/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46051291311/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((213233/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c135 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((923379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 492507/5000000) (δ := 10253/1000000000) (ψ := -122331/1000000) 205 160
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t135 : ((397337091899/5000000000000 : ℚ) : ℝ) ≤ stT205 135 := by
  have hc : ((923329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((397337091899/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((923329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c136 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-82459/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 953463/2000000) (δ := 10353/1000000000) (ψ := -122331/1000000) 205 160
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t136 : ((-141437467899/5000000000000 : ℚ) : ℝ) ≤ stT205 136 := by
  have hc : ((-164943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141437467899/5000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-164943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c137 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-482259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3593011/5000000) (δ := 5173/500000000) (ψ := -122331/1000000) 205 161
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t137 : ((-51505399209/625000000000 : ℚ) : ℝ) ≤ stT205 137 := by
  have hc : ((-120571/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51505399209/625000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-120571/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c138 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((93099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3458763/10000000) (δ := 10257/1000000000) (ψ := -122331/1000000) 205 161
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t138 : ((4951862559/312500000000 : ℚ) : ℝ) ≤ stT205 138 := by
  have hc : ((46537/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4951862559/312500000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((46537/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c139 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((248833/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 241641/10000000) (δ := 10357/1000000000) (ψ := -122331/1000000) 205 161
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t139 : ((105523281127/1250000000000 : ℚ) : ℝ) ≤ stT205 139 := by
  have hc : ((497641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105523281127/1250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((497641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c140 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((2299/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3915497/10000000) (δ := 10257/1000000000) (ψ := -122331/1000000) 205 161
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t140 : ((480470049/1250000000000 : ℚ) : ℝ) ≤ stT205 140 := by
  have hc : ((1137/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((480470049/1250000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((1137/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c141 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-496621/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1890791/2500000) (δ := 5223/500000000) (ψ := -122331/1000000) 205 161
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t141 : ((-26140713887/312500000000 : ℚ) : ℝ) ≤ stT205 141 := by
  have hc : ((-248323/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26140713887/312500000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-248323/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c142 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-236097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4522859/10000000) (δ := 5169/500000000) (ψ := -122331/1000000) 205 162
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t142 : ((-99085155877/5000000000000 : ℚ) : ℝ) ≤ stT205 142 := by
  have hc : ((-236147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99085155877/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-236147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c143 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((466067/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -926339/10000000) (δ := 5169/500000000) (ψ := -122331/1000000) 205 162
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t143 : ((97430973541/1250000000000 : ℚ) : ℝ) ≤ stT205 143 := by
  have hc : ((233021/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97430973541/1250000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((233021/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c144 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((15331/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2645069/10000000) (δ := 2073/200000000) (ψ := -122331/1000000) 205 162
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t144 : ((204392418243/5000000000000 : ℚ) : ℝ) ≤ stT205 144 := by
  have hc : ((245271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204392418243/5000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((245271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c145 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-393501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 247673/400000) (δ := 2053/200000000) (ψ := -122331/1000000) 205 162
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t145 : ((-32680563433/500000000000 : ℚ) : ℝ) ≤ stT205 145 := by
  have hc : ((-196763/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32680563433/500000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-196763/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c146 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-73571/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5993777/10000000) (δ := 321/31250000) (ψ := -122331/1000000) 205 163
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t146 : ((-3805746191/62500000000 : ℚ) : ℝ) ≤ stT205 146 := by
  have hc : ((-9197/12500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3805746191/62500000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-9197/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c147 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((108363/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2495503/10000000) (δ := 2593/250000000) (ψ := -122331/1000000) 205 163
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t147 : ((44684018729/1000000000000 : ℚ) : ℝ) ≤ stT205 147 := by
  have hc : ((108353/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44684018729/1000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((108353/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c148 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((184857/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 979093/10000000) (δ := 321/31250000) (ψ := -122331/1000000) 205 163
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t148 : ((75971562459/1000000000000 : ℚ) : ℝ) ≤ stT205 148 := by
  have hc : ((184847/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75971562459/1000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((184847/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c149 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-99987/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4430319/10000000) (δ := 10331/1000000000) (ψ := -122331/1000000) 205 163
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t149 : ((-640101803/39062500000 : ℚ) : ℝ) ≤ stT205 149 := by
  have hc : ((-25003/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-640101803/39062500000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-25003/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c150 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-499999/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7849583/10000000) (δ := 2581/250000000) (ψ := -122331/1000000) 205 164
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t150 : ((-51033511991/625000000000 : ℚ) : ℝ) ≤ stT205 150 := by
  have hc : ((-62503/62500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51033511991/625000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-62503/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c151 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-205421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -177769/400000) (δ := 10379/1000000000) (ψ := -122331/1000000) 205 164
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t151 : ((-167210039619/10000000000000 : ℚ) : ℝ) ≤ stT205 151 := by
  have hc : ((-205471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167210039619/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-205471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c152 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((455613/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1061367/10000000) (δ := 1303/125000000) (ψ := -122331/1000000) 205 164
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t152 : ((92382653979/1250000000000 : ℚ) : ℝ) ≤ stT205 152 := by
  have hc : ((113897/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92382653979/1250000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((113897/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c153 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((606043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2299301/10000000) (δ := 10279/1000000000) (ψ := -122331/1000000) 205 164
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t153 : ((122479063209/2500000000000 : ℚ) : ℝ) ≤ stT205 153 := by
  have hc : ((605993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122479063209/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((605993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c154 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-632237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1127617/2000000) (δ := 10379/1000000000) (ψ := -122331/1000000) 205 164
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t154 : ((-509511407201/10000000000000 : ℚ) : ℝ) ≤ stT205 154 := by
  have hc : ((-632287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-509511407201/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-632287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c155 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-904537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3376361/5000000) (δ := 5193/500000000) (ψ := -122331/1000000) 205 165
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t155 : ((-36329118507/500000000000 : ℚ) : ℝ) ≤ stT205 155 := by
  have hc : ((-904587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36329118507/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-904587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c156 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((23367/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1728443/5000000) (δ := 5143/500000000) (ψ := -122331/1000000) 205 165
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t156 : ((116897193/7812500000 : ℚ) : ℝ) ≤ stT205 156 := by
  have hc : ((93443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116897193/7812500000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((93443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c157 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((249337/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -91057/5000000) (δ := 10417/1000000000) (ψ := -122331/1000000) 205 165
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t157 : ((198982392907/2500000000000 : ℚ) : ℝ) ≤ stT205 157 := by
  have hc : ((498649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198982392907/2500000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((498649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c158 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((13417/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3071851/10000000) (δ := 10417/1000000000) (ψ := -122331/1000000) 205 165
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t158 : ((2134479431/80000000000 : ℚ) : ℝ) ≤ stT205 158 := by
  have hc : ((2683/8000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2134479431/80000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((2683/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c159 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-203547/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1576329/2500000) (δ := 10417/1000000000) (ψ := -122331/1000000) 205 165
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t159 : ((-80716634297/1250000000000 : ℚ) : ℝ) ≤ stT205 159 := by
  have hc : ((-407119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80716634297/1250000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-407119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c160 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-393211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6189477/10000000) (δ := 1031/100000000) (ψ := -122331/1000000) 205 166
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t160 : ((-7772014613/125000000000 : ℚ) : ℝ) ≤ stT205 160 := by
  have hc : ((-98309/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7772014613/125000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-98309/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c161 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((9093/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1498173/5000000) (δ := 1041/100000000) (ψ := -122331/1000000) 205 166
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t161 : ((2866119637/100000000000 : ℚ) : ℝ) ≤ stT205 161 := by
  have hc : ((36367/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2866119637/100000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((36367/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c162 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((997493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 88527/5000000) (δ := 1041/100000000) (ψ := -122331/1000000) 205 166
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t162 : ((391832515791/5000000000000 : ℚ) : ℝ) ≤ stT205 162 := by
  have hc : ((997443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((391832515791/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((997443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c163 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((236173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 208183/625000) (δ := 1031/100000000) (ψ := -122331/1000000) 205 166
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t163 : ((9247285049/500000000000 : ℚ) : ℝ) ≤ stT205 163 := by
  have hc : ((236123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9247285049/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((236123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c164 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-849689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6465481/10000000) (δ := 10393/1000000000) (ψ := -122331/1000000) 205 166
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t164 : ((-663534843191/10000000000000 : ℚ) : ℝ) ≤ stT205 164 := by
  have hc : ((-849739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-663534843191/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-849739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c165 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-38537/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1225399/2000000) (δ := 103/10000000) (ψ := -122331/1000000) 205 167
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t165 : ((-60005924421/1000000000000 : ℚ) : ℝ) ≤ stT205 165 := by
  have hc : ((-77079/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60005924421/1000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-77079/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c166 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((351029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -757579/2500000) (δ := 13/1250000) (ψ := -122331/1000000) 205 167
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t166 : ((5448247017/200000000000 : ℚ) : ℝ) ≤ stT205 166 := by
  have hc : ((350979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5448247017/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((350979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c167 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((999817/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4781/1000000) (δ := 103/10000000) (ψ := -122331/1000000) 205 167
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t167 : ((773642699241/10000000000000 : ℚ) : ℝ) ≤ stT205 167 := by
  have hc : ((999767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((773642699241/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((999767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c168 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((321963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1553743/5000000) (δ := 10303/1000000000) (ψ := -122331/1000000) 205 167
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t168 : ((62090257527/2500000000000 : ℚ) : ℝ) ≤ stT205 168 := by
  have hc : ((321913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62090257527/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((321913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c169 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-48521/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6149071/10000000) (δ := 10303/1000000000) (ψ := -122331/1000000) 205 167
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t169 : ((-298610089583/5000000000000 : ℚ) : ℝ) ≤ stT205 169 := by
  have hc : ((-388193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-298610089583/5000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-388193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c170 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-864081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51057/78125) (δ := 2059/200000000) (ψ := -122331/1000000) 205 168
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t170 : ((-132551646483/2000000000000 : ℚ) : ℝ) ≤ stT205 170 := by
  have hc : ((-864131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132551646483/2000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-864131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c171 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((79177/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -441179/1250000) (δ := 2577/250000000) (ψ := -122331/1000000) 205 168
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t171 : ((3783064893/312500000000 : ℚ) : ℝ) ≤ stT205 171 := by
  have hc : ((4947/31250 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3783064893/312500000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((4947/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c172 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((976669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -67637/1250000) (δ := 2059/200000000) (ψ := -122331/1000000) 205 168
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t172 : ((186166043637/2500000000000 : ℚ) : ℝ) ≤ stT205 172 := by
  have hc : ((976619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((186166043637/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((976619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c173 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((140919/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1214959/5000000) (δ := 2577/250000000) (ψ := -122331/1000000) 205 168
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t173 : ((42851639341/1000000000000 : ℚ) : ℝ) ≤ stT205 173 := by
  have hc : ((281813/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42851639341/1000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((281813/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c174 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-110061/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2691907/5000000) (δ := 2059/200000000) (ψ := -122331/1000000) 205 168
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t174 : ((-83444715029/2000000000000 : ℚ) : ℝ) ≤ stT205 174 := by
  have hc : ((-110071/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83444715029/2000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-110071/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c175 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-982617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1477433/2000000) (δ := 2083/200000000) (ψ := -122331/1000000) 205 169
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t175 : ((-742826482643/10000000000000 : ℚ) : ℝ) ≤ stT205 175 := by
  have hc : ((-982667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-742826482643/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-982667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c176 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-6697/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -223347/500000) (δ := 2083/200000000) (ψ := -122331/1000000) 205 169
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t176 : ((-80787771883/5000000000000 : ℚ) : ℝ) ≤ stT205 176 := by
  have hc : ((-107177/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80787771883/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-107177/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c177 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((162159/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -781609/5000000) (δ := 643/62500000) (ψ := -122331/1000000) 205 169
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t177 : ((60939323627/1000000000000 : ℚ) : ℝ) ≤ stT205 177 := by
  have hc : ((162149/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60939323627/1000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((162149/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c178 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((215747/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 264821/2000000) (δ := 2083/200000000) (ψ := -122331/1000000) 205 169
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t178 : ((323399391039/5000000000000 : ℚ) : ℝ) ≤ stT205 178 := by
  have hc : ((431469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((323399391039/5000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((431469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c179 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-107111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4195283/10000000) (δ := 2597/250000000) (ψ := -122331/1000000) 205 169
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t179 : ((-20023997299/2500000000000 : ℚ) : ℝ) ≤ stT205 179 := by
  have hc : ((-107161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20023997299/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-107161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c180 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-474393/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7050421/10000000) (δ := 2063/200000000) (ψ := -122331/1000000) 205 169
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t180 : ((-44201287851/625000000000 : ℚ) : ℝ) ≤ stT205 180 := by
  have hc : ((-237209/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44201287851/625000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-237209/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c181 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-343183/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -581819/1000000) (δ := 10281/1000000000) (ψ := -122331/1000000) 205 170
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t181 : ((-6377619759/125000000000 : ℚ) : ℝ) ≤ stT205 181 := by
  have hc : ((-42901/62500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6377619759/125000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-42901/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c182 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((911/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74863/250000) (δ := 10281/1000000000) (ψ := -122331/1000000) 205 170
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t182 : ((5401481463/200000000000 : ℚ) : ℝ) ≤ stT205 182 := by
  have hc : ((7287/20000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5401481463/200000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((7287/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c183 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((39889/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46569/2500000) (δ := 5161/500000000) (ψ := -122331/1000000) 205 170
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t183 : ((29485308027/400000000000 : ℚ) : ℝ) ≤ stT205 183 := by
  have hc : ((39887/40000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29485308027/400000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((39887/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c184 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((503927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 651661/2500000) (δ := 5161/500000000) (ψ := -122331/1000000) 205 170
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t184 : ((371462659293/10000000000000 : ℚ) : ℝ) ≤ stT205 184 := by
  have hc : ((503877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((371462659293/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((503877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c185 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-137629/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1076889/2000000) (δ := 10281/1000000000) (ψ := -122331/1000000) 205 170
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t185 : ((-40478438169/1000000000000 : ℚ) : ℝ) ≤ stT205 185 := by
  have hc : ((-275283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40478438169/1000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-275283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c186 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-124141/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7560733/10000000) (δ := 10329/1000000000) (ψ := -122331/1000000) 205 171
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t186 : ((-91029233001/1250000000000 : ℚ) : ℝ) ≤ stT205 186 := by
  have hc : ((-496589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91029233001/1250000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-496589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c187 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-173461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1203177/2500000) (δ := 10329/1000000000) (ψ := -122331/1000000) 205 171
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t187 : ((-63432813839/2500000000000 : ℚ) : ℝ) ≤ stT205 187 := by
  have hc : ((-86743/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63432813839/2500000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-86743/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c188 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((336789/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -64981/312500) (δ := 5137/500000000) (ψ := -122331/1000000) 205 171
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t188 : ((15350629221/312500000000 : ℚ) : ℝ) ≤ stT205 188 := by
  have hc : ((84191/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15350629221/312500000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((84191/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c189 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((120933/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39967/625000) (δ := 10329/1000000000) (ψ := -122331/1000000) 205 171
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t189 : ((10995143817/156250000000 : ℚ) : ℝ) ≤ stT205 189 := by
  have hc : ((483707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10995143817/156250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((483707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c190 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((115557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1671967/5000000) (δ := 5187/500000000) (ψ := -122331/1000000) 205 171
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t190 : ((5238480827/312500000000 : ℚ) : ℝ) ≤ stT205 190 := by
  have hc : ((28883/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5238480827/312500000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((28883/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c191 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-746579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1508563/2500000) (δ := 10329/1000000000) (ψ := -122331/1000000) 205 171
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t191 : ((-21609683147/400000000000 : ℚ) : ℝ) ≤ stT205 191 := by
  have hc : ((-746629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21609683147/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-746629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c192 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-188377/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -437343/625000) (δ := 10367/1000000000) (ψ := -122331/1000000) 205 172
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t192 : ((-16994579657/250000000000 : ℚ) : ℝ) ≤ stT205 192 := by
  have hc : ((-188387/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16994579657/250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-188387/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c193 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-162541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4335153/10000000) (δ := 10367/1000000000) (ψ := -122331/1000000) 205 172
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t193 : ((-14629450407/1250000000000 : ℚ) : ℝ) ≤ stT205 193 := by
  have hc : ((-162591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14629450407/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-162591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c194 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((48809/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1686553/10000000) (δ := 10367/1000000000) (ψ := -122331/1000000) 205 172
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t194 : ((140162273613/2500000000000 : ℚ) : ℝ) ≤ stT205 194 := by
  have hc : ((390447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140162273613/2500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((390447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c195 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((9289/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 189683/2000000) (δ := 323/31250000) (ψ := -122331/1000000) 205 172
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t195 : ((6651624889/100000000000 : ℚ) : ℝ) ≤ stT205 195 := by
  have hc : ((18577/20000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6651624889/100000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((18577/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c196 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((2847/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 223119/625000) (δ := 2609/250000000) (ψ := -122331/1000000) 205 172
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t196 : ((203285511/20000000000 : ℚ) : ℝ) ≤ stT205 196 := by
  have hc : ((1423/10000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203285511/20000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((1423/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c197 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-391797/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6178067/10000000) (δ := 10367/1000000000) (ψ := -122331/1000000) 205 172
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t197 : ((-139580906081/2500000000000 : ℚ) : ℝ) ≤ stT205 197 := by
  have hc : ((-195911/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139580906081/2500000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-195911/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c198 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-933189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1386991/2000000) (δ := 10359/1000000000) (ψ := -122331/1000000) 205 173
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t198 : ((-66322496013/1000000000000 : ℚ) : ℝ) ≤ stT205 198 := by
  have hc : ((-933239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66322496013/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-933239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c199 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-169613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2176541/5000000) (δ := 1293/125000000) (ψ := -122331/1000000) 205 173
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t199 : ((-60135523383/5000000000000 : ℚ) : ℝ) ≤ stT205 199 := by
  have hc : ((-169663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60135523383/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-169663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c200 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((188991/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -111511/625000) (δ := 10259/1000000000) (ψ := -122331/1000000) 205 173
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t200 : ((133627831221/2500000000000 : ℚ) : ℝ) ≤ stT205 200 := by
  have hc : ((377957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133627831221/2500000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((377957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c201 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((952703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 771969/10000000) (δ := 10259/1000000000) (ψ := -122331/1000000) 205 173
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t201 : ((134389806057/2000000000000 : ℚ) : ℝ) ≤ stT205 201 := by
  have hc : ((952653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134389806057/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((952653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c202 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((121111/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3315353/10000000) (δ := 1293/125000000) (ψ := -122331/1000000) 205 173
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t202 : ((42597873171/2500000000000 : ℚ) : ℝ) ≤ stT205 202 := by
  have hc : ((60543/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42597873171/2500000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((60543/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c203 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-8681/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 730779/1250000) (δ := 2611/250000000) (ψ := -122331/1000000) 205 173
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t203 : ((-48746490939/1000000000000 : ℚ) : ℝ) ≤ stT205 203 := by
  have hc : ((-69453/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48746490939/1000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-69453/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c204 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-979209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7343307/10000000) (δ := 647/62500000) (ψ := -122331/1000000) 205 174
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t204 : ((-685619375519/10000000000000 : ℚ) : ℝ) ≤ stT205 204 := by
  have hc : ((-979259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-685619375519/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-979259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c205 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-178043/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2418591/5000000) (δ := 647/62500000) (ψ := -122331/1000000) 205 174
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t205 : ((-31092052827/1250000000000 : ℚ) : ℝ) ≤ stT205 205 := by
  have hc : ((-44517/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31092052827/1250000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-44517/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c206 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((118393/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1171627/5000000) (δ := 10351/1000000000) (ψ := -122331/1000000) 205 174
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t206 : ((82481342739/2000000000000 : ℚ) : ℝ) ≤ stT205 206 := by
  have hc : ((118383/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82481342739/2000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((118383/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c207 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((15601/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69289/5000000) (δ := 647/62500000) (ψ := -122331/1000000) 205 174
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t207 : ((43371603367/625000000000 : ℚ) : ℝ) ≤ stT205 207 := by
  have hc : ((499207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43371603367/625000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((499207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c208 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((7864/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 260847/1000000) (δ := 10451/1000000000) (ψ := -122331/1000000) 205 174
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t208 : ((1395752781/40000000000 : ℚ) : ℝ) ≤ stT205 208 := by
  have hc : ((251623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1395752781/40000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((251623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c209 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-6878/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2533261/5000000) (δ := 2563/250000000) (ψ := -122331/1000000) 205 174
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t209 : ((-30452199503/1000000000000 : ℚ) : ℝ) ≤ stT205 209 := by
  have hc : ((-220121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30452199503/1000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-220121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c210 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-61919/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3756419/5000000) (δ := 647/62500000) (ψ := -122331/1000000) 205 174
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t210 : ((-170921412441/2500000000000 : ℚ) : ℝ) ≤ stT205 210 := by
  have hc : ((-495377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170921412441/2500000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-495377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c211 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-133877/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5760443/10000000) (δ := 2089/200000000) (ψ := -122331/1000000) 205 175
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t211 : ((-92171693523/2000000000000 : ℚ) : ℝ) ≤ stT205 211 := by
  have hc : ((-133887/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92171693523/2000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-133887/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c212 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((233699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3337291/10000000) (δ := 5179/500000000) (ψ := -122331/1000000) 205 175
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t212 : ((80235300249/5000000000000 : ℚ) : ℝ) ≤ stT205 212 := by
  have hc : ((233649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80235300249/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((233649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c213 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((233063/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -462759/5000000) (δ := 2089/200000000) (ψ := -122331/1000000) 205 175
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t213 : ((79841702997/1250000000000 : ℚ) : ℝ) ≤ stT205 213 := by
  have hc : ((466101/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79841702997/1250000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((466101/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c214 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((166189/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1474981/10000000) (δ := 2069/200000000) (ψ := -122331/1000000) 205 175
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t214 : ((22719494343/400000000000 : ℚ) : ℝ) ≤ stT205 214 := by
  have hc : ((166179/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22719494343/400000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((166179/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c215 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((25091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60379/156250) (δ := 2069/200000000) (ψ := -122331/1000000) 205 175
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t215 : ((8538905877/5000000000000 : ℚ) : ℝ) ≤ stT205 215 := by
  have hc : ((25041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8538905877/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((25041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c216 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-159867/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6242461/10000000) (δ := 2069/200000000) (ψ := -122331/1000000) 205 175
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t216 : ((-54391274539/1000000000000 : ℚ) : ℝ) ≤ stT205 216 := by
  have hc : ((-159877/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54391274539/1000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-159877/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c217 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-119333/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1774579/2500000) (δ := 5169/500000000) (ψ := -122331/1000000) 205 176
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t217 : ((-64810282533/1000000000000 : ℚ) : ℝ) ≤ stT205 217 := by
  have hc : ((-477357/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64810282533/1000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-477357/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c218 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-160129/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -948399/2000000) (δ := 5219/500000000) (ψ := -122331/1000000) 205 176
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t218 : ((-27117515511/1250000000000 : ℚ) : ℝ) ≤ stT205 218 := by
  have hc : ((-80077/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27117515511/1250000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-80077/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c219 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((574687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -599109/2500000) (δ := 5169/500000000) (ψ := -122331/1000000) 205 176
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t219 : ((388303482469/10000000000000 : ℚ) : ℝ) ≤ stT205 219 := by
  have hc : ((574637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((388303482469/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((574637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c220 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((999697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15397/2500000) (δ := 2073/200000000) (ψ := -122331/1000000) 205 176
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t220 : ((673961007753/10000000000000 : ℚ) : ℝ) ≤ stT205 220 := by
  have hc : ((999647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((673961007753/10000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((999647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c221 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((308811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1131351/5000000) (δ := 2073/200000000) (ψ := -122331/1000000) 205 176
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t221 : ((3245495253/78125000000 : ℚ) : ℝ) ≤ stT205 221 := by
  have hc : ((154393/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3245495253/78125000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((154393/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c222 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-51373/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2288217/5000000) (δ := 5169/500000000) (ψ := -122331/1000000) 205 176
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t222 : ((-34486060131/2000000000000 : ℚ) : ℝ) ≤ stT205 222 := by
  have hc : ((-51383/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34486060131/2000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-51383/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c223 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-231259/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3439907/5000000) (δ := 5169/500000000) (ψ := -122331/1000000) 205 176
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t223 : ((-6194838399/100000000000 : ℚ) : ℝ) ≤ stT205 223 := by
  have hc : ((-462543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6194838399/100000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-462543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c224 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-216009/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -653507/1000000) (δ := 2593/250000000) (ψ := -122331/1000000) 205 177
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t224 : ((-144335629311/2500000000000 : ℚ) : ℝ) ≤ stT205 224 := by
  have hc : ((-432043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144335629311/2500000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-432043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c225 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-129713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -425219/1000000) (δ := 2593/250000000) (ψ := -122331/1000000) 205 177
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t225 : ((-86508709921/10000000000000 : ℚ) : ℝ) ≤ stT205 225 := by
  have hc : ((-129763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86508709921/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-129763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c226 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((70257/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1979483/10000000) (δ := 323/15625000) (ψ := -122331/1000000) 205 177
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t226 : ((1168273197/25000000000 : ℚ) : ℝ) ≤ stT205 226 := by
  have hc : ((17563/25000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1168273197/25000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((17563/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c227 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((993589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 28323/1000000) (δ := 2593/250000000) (ψ := -122331/1000000) 205 177
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t227 : ((659434685697/10000000000000 : ℚ) : ℝ) ≤ stT205 227 := by
  have hc : ((993539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((659434685697/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((993539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c228 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((264069/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 101439/400000) (δ := 2593/250000000) (ψ := -122331/1000000) 205 177
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t228 : ((21858420463/625000000000 : ℚ) : ℝ) ≤ stT205 228 := by
  have hc : ((66011/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21858420463/625000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((66011/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c229 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-334199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7467/15625) (δ := 2593/250000000) (ψ := -122331/1000000) 205 177
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t229 : ((-220878089931/10000000000000 : ℚ) : ℝ) ≤ stT205 229 := by
  have hc : ((-334249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220878089931/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-334249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c230 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-943819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1752999/2500000) (δ := 321/31250000) (ψ := -122331/1000000) 205 177
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t230 : ((-622369285089/10000000000000 : ℚ) : ℝ) ≤ stT205 230 := by
  have hc : ((-943869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-622369285089/10000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-943869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c231 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-425587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6472537/10000000) (δ := 10379/1000000000) (ψ := -122331/1000000) 205 178
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t231 : ((-2187752083/39062500000 : ℚ) : ℝ) ≤ stT205 231 := by
  have hc : ((-106403/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2187752083/39062500000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-106403/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c232 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-132311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2129371/5000000) (δ := 10379/1000000000) (ψ := -122331/1000000) 205 178
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t232 : ((-86899364413/10000000000000 : ℚ) : ℝ) ≤ stT205 232 := by
  have hc : ((-132361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86899364413/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-132361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c233 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((27237/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2054429/10000000) (δ := 1303/125000000) (ψ := -122331/1000000) 205 178
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t233 : ((3568444087/80000000000 : ℚ) : ℝ) ≤ stT205 233 := by
  have hc : ((5447/8000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3568444087/80000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((5447/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c234 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((499211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 28091/2000000) (δ := 2581/250000000) (ψ := -122331/1000000) 205 178
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t234 : ((4079098399/62500000000 : ℚ) : ℝ) ≤ stT205 234 := by
  have hc : ((249593/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4079098399/62500000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((249593/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c235 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((298763/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58149/250000) (δ := 2581/250000000) (ψ := -122331/1000000) 205 178
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t235 : ((12179697629/312500000000 : ℚ) : ℝ) ≤ stT205 235 := by
  have hc : ((149369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12179697629/312500000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((149369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c236 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-45611/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4502189/10000000) (δ := 10279/1000000000) (ψ := -122331/1000000) 205 178
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t236 : ((-5939352369/400000000000 : ℚ) : ℝ) ≤ stT205 236 := by
  have hc : ((-45621/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5939352369/400000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-45621/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c237 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-222447/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6669193/10000000) (δ := 10379/1000000000) (ψ := -122331/1000000) 205 178
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t237 : ((-28900603483/500000000000 : ℚ) : ℝ) ≤ stT205 237 := by
  have hc : ((-444919/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28900603483/500000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-444919/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c238 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-925199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6880889/10000000) (δ := 10387/1000000000) (ψ := -122331/1000000) 205 179
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t238 : ((-149937525699/2500000000000 : ℚ) : ℝ) ≤ stT205 238 := by
  have hc : ((-925249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149937525699/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-925249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c239 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-316479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1183007/2500000) (δ := 10287/1000000000) (ψ := -122331/1000000) 205 179
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t239 : ((-204745834063/10000000000000 : ℚ) : ℝ) ≤ stT205 239 := by
  have hc : ((-316529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204745834063/10000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-316529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c240 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((508931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -324017/1250000) (δ := 651/62500000) (ψ := -122331/1000000) 205 179
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t240 : ((328481158857/10000000000000 : ℚ) : ℝ) ≤ stT205 240 := by
  have hc : ((508881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((328481158857/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((508881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c241 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((196607/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -461161/10000000) (δ := 651/62500000) (ψ := -122331/1000000) 205 179
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t241 : ((31659784283/500000000000 : ℚ) : ℝ) ≤ stT205 241 := by
  have hc : ((196597/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31659784283/500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((196597/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c242 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((787287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1660999/10000000) (δ := 651/62500000) (ψ := -122331/1000000) 205 179
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t242 : ((63256854661/1250000000000 : ℚ) : ℝ) ≤ stT205 242 := by
  have hc : ((787237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63256854661/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((787237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c243 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((61/1000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 943599/2500000) (δ := 10387/1000000000) (ψ := -122331/1000000) 205 179
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t243 : ((1563977/400000000 : ℚ) : ℝ) ≤ stT205 243 := by
  have hc : ((1219/20000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1563977/400000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((1219/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c244 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-43993/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5879131/10000000) (δ := 10387/1000000000) (ψ := -122331/1000000) 205 179
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t244 : ((-45065054853/1000000000000 : ℚ) : ℝ) ≤ stT205 244 := by
  have hc : ((-351969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45065054853/1000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-351969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c245 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-124853/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7732733/10000000) (δ := 10297/500000000) (ψ := -122331/1000000) 205 180
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t245 : ((-319078812249/5000000000000 : ℚ) : ℝ) ≤ stT205 245 := by
  have hc : ((-499437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-319078812249/5000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-499437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c246 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-317211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5645141/10000000) (δ := 5197/500000000) (ψ := -122331/1000000) 205 180
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t246 : ((-50565594293/1250000000000 : ℚ) : ℝ) ≤ stT205 246 := by
  have hc : ((-79309/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50565594293/1250000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-79309/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c247 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((143883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3566031/10000000) (δ := 5197/500000000) (ψ := -122331/1000000) 205 180
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t247 : ((22879659143/2500000000000 : ℚ) : ℝ) ≤ stT205 247 := by
  have hc : ((143833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22879659143/2500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((143833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c248 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((82639/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -747663/5000000) (δ := 5197/500000000) (ψ := -122331/1000000) 205 180
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t248 : ((5247259/100000000 : ℚ) : ℝ) ≤ stT205 248 := by
  have hc : ((41317/50000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5247259/100000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((41317/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c249 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((974389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 22681/400000) (δ := 5147/500000000) (ψ := -122331/1000000) 205 180
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t249 : ((154365502109/2500000000000 : ℚ) : ℝ) ≤ stT205 249 := by
  have hc : ((974339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154365502109/2500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((974339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c250 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((498897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 327647/1250000) (δ := 10309/1000000000) (ψ := -122331/1000000) 205 180
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t250 : ((63099655877/2000000000000 : ℚ) : ℝ) ≤ stT205 250 := by
  have hc : ((498847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63099655877/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((498847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c251 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-291729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1166769/2500000) (δ := 10309/1000000000) (ψ := -122331/1000000) 205 180
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t251 : ((-36833889181/2000000000000 : ℚ) : ℝ) ≤ stT205 251 := by
  have hc : ((-291779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).2
  have h0 : (0:ℝ) ≤ ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36833889181/2000000000000 : ℚ) : ℝ)
      = ((126239/2000000 : ℚ) : ℝ) * ((-291779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c252 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-896203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6704827/10000000) (δ := 10409/1000000000) (ψ := -122331/1000000) 205 180
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t252 : ((-564586511073/10000000000000 : ℚ) : ℝ) ≤ stT205 252 := by
  have hc : ((-896253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).2
  have h0 : (0:ℝ) ≤ ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-564586511073/10000000000000 : ℚ) : ℝ)
      = ((629941/10000000 : ℚ) : ℝ) * ((-896253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c253 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-938609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6973431/10000000) (δ := 5151/500000000) (ψ := -122331/1000000) 205 181
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t253 : ((-118026044001/2000000000000 : ℚ) : ℝ) ≤ stT205 253 := by
  have hc : ((-938659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118026044001/2000000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-938659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c254 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-39851/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4951721/10000000) (δ := 5151/500000000) (ψ := -122331/1000000) 205 181
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t254 : ((-6105441/244140625 : ℚ) : ℝ) ≤ stT205 254 := by
  have hc : ((-2491/6250 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6105441/244140625 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-2491/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c255 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((3083/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -587591/2000000) (δ := 5201/500000000) (ψ := -122331/1000000) 205 181
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t255 : ((603249407/25000000000 : ℚ) : ℝ) ≤ stT205 255 := by
  have hc : ((15413/40000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).1
  have hw2 : ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39139/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((603249407/25000000000 : ℚ) : ℝ)
      = ((39139/625000 : ℚ) : ℝ) * ((15413/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c256 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((931299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -932081/10000000) (δ := 5151/500000000) (ψ := -122331/1000000) 205 181
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t256 : ((931249/16000000 : ℚ) : ℝ) ≤ stT205 256 := by
  have hc : ((931249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).1
  have hw2 : ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((931249/16000000 : ℚ) : ℝ)
      = ((1/16 : ℚ) : ℝ) * ((931249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c257 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((910469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33311/312500) (δ := 10401/1000000000) (ψ := -122331/1000000) 205 181
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t257 : ((283951492329/5000000000000 : ℚ) : ℝ) ≤ stT205 257 := by
  have hc : ((910419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((283951492329/5000000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((910419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c258 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((341299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 611249/2000000) (δ := 5201/500000000) (ψ := -122331/1000000) 205 181
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t258 : ((53113018107/2500000000000 : ℚ) : ℝ) ≤ stT205 258 := by
  have hc : ((341249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53113018107/2500000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((341249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c259 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-430227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1259713/2500000) (δ := 10401/1000000000) (ψ := -122331/1000000) 205 181
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t259 : ((-26736121949/1000000000000 : ℚ) : ℝ) ≤ stT205 259 := by
  have hc : ((-430277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).2
  have h0 : (0:ℝ) ≤ ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26736121949/1000000000000 : ℚ) : ℝ)
      = ((62137/1000000 : ℚ) : ℝ) * ((-430277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c260 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-47203/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3506911/5000000) (δ := 10401/1000000000) (ψ := -122331/1000000) 205 181
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t260 : ((-29275623757/500000000000 : ℚ) : ℝ) ≤ stT205 260 := by
  have hc : ((-94411/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29275623757/500000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-94411/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c261 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-45003/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6726757/10000000) (δ := 2079/200000000) (ψ := -122331/1000000) 205 182
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t261 : ((-11143091767/200000000000 : ℚ) : ℝ) ≤ stT205 261 := by
  have hc : ((-90011/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11143091767/200000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-90011/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c262 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-329681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -953381/2000000) (δ := 7727/250000000) (ψ := -122331/1000000) 205 182
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t262 : ((-203708800993/10000000000000 : ℚ) : ℝ) ≤ stT205 262 := by
  have hc : ((-329731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-203708800993/10000000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-329731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c263 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((430441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2814537/10000000) (δ := 2079/200000000) (ψ := -122331/1000000) 205 182
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t263 : ((132695140383/5000000000000 : ℚ) : ℝ) ≤ stT205 263 := by
  have hc : ((430391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132695140383/5000000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((430391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c264 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((470059/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -217387/2500000) (δ := 6159/200000000) (ψ := -122331/1000000) 205 182
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t264 : ((144642857769/2500000000000 : ℚ) : ℝ) ≤ stT205 264 := by
  have hc : ((235017/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144642857769/2500000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((235017/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c265 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((910119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1068061/10000000) (δ := 2577/250000000) (ψ := -122331/1000000) 205 182
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t265 : ((111810167271/2000000000000 : ℚ) : ℝ) ≤ stT205 265 := by
  have hc : ((910069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111810167271/2000000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((910069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c266 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((362957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 374799/1250000) (δ := 2059/200000000) (ψ := -122331/1000000) 205 182
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t266 : ((222512435073/10000000000000 : ℚ) : ℝ) ≤ stT205 266 := by
  have hc : ((362907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).1
  have hw2 : ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((613139/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222512435073/10000000000000 : ℚ) : ℝ)
      = ((613139/10000000 : ℚ) : ℝ) * ((362907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c267 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-3099/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2460723/5000000) (δ := 2577/250000000) (ψ := -122331/1000000) 205 182
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t267 : ((-9484024527/400000000000 : ℚ) : ℝ) ≤ stT205 267 := by
  have hc : ((-15497/40000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9484024527/400000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-15497/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c268 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-459223/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 273493/400000) (δ := 1301/125000000) (ψ := -122331/1000000) 205 182
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t268 : ((-547911567/9765625000 : ℚ) : ℝ) ≤ stT205 268 := by
  have hc : ((-28703/31250 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-547911567/9765625000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-28703/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c269 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-468503/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1740471/2500000) (δ := 2597/250000000) (ψ := -122331/1000000) 205 183
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t269 : ((-17854167213/312500000000 : ℚ) : ℝ) ≤ stT205 269 := by
  have hc : ((-29283/31250 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).2
  have h0 : (0:ℝ) ≤ ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17854167213/312500000000 : ℚ) : ℝ)
      = ((609711/10000000 : ℚ) : ℝ) * ((-29283/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c270 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-2737/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5060201/10000000) (δ := 2063/200000000) (ψ := -122331/1000000) 205 183
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t270 : ((-26654022057/1000000000000 : ℚ) : ℝ) ≤ stT205 270 := by
  have hc : ((-43797/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).2
  have h0 : (0:ℝ) ≤ ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26654022057/1000000000000 : ℚ) : ℝ)
      = ((608581/10000000 : ℚ) : ℝ) * ((-43797/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c271 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((299893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -158277/500000) (δ := 643/62500000) (ψ := -122331/1000000) 205 183
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t271 : ((5691919669/312500000000 : ℚ) : ℝ) ≤ stT205 271 := by
  have hc : ((299843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5691919669/312500000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((299843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c272 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((436089/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12779/100000) (δ := 643/62500000) (ψ := -122331/1000000) 205 183
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t272 : ((8262581553/156250000000 : ℚ) : ℝ) ≤ stT205 272 := by
  have hc : ((13627/15625 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).1
  have hw2 : ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8262581553/156250000000 : ℚ) : ℝ)
      = ((606339/10000000 : ℚ) : ℝ) * ((13627/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c273 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((971069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 602821/10000000) (δ := 2597/250000000) (ψ := -122331/1000000) 205 183
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t273 : ((587686916313/10000000000000 : ℚ) : ℝ) ≤ stT205 273 := by
  have hc : ((971019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).1
  have hw2 : ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((605227/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((587686916313/10000000000000 : ℚ) : ℝ)
      = ((605227/10000000 : ℚ) : ℝ) * ((971019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c274 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((548113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1238363/5000000) (δ := 2597/250000000) (ψ := -122331/1000000) 205 183
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t274 : ((165548457843/5000000000000 : ℚ) : ℝ) ≤ stT205 274 := by
  have hc : ((548063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).1
  have hw2 : ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((302061/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165548457843/5000000000000 : ℚ) : ℝ)
      = ((302061/5000000 : ℚ) : ℝ) * ((548063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c275 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-82959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4343713/10000000) (δ := 2083/200000000) (ψ := -122331/1000000) 205 183
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t275 : ((-6255157579/625000000000 : ℚ) : ℝ) ≤ stT205 275 := by
  have hc : ((-10373/62500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6255157579/625000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-10373/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c276 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-789993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1240797/2000000) (δ := 643/62500000) (ψ := -122331/1000000) 205 183
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t276 : ((-47555058299/1000000000000 : ℚ) : ℝ) ≤ stT205 276 := by
  have hc : ((-790043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).2
  have h0 : (0:ℝ) ≤ ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47555058299/1000000000000 : ℚ) : ℝ)
      = ((60193/1000000 : ℚ) : ℝ) * ((-790043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c277 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-996687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7650419/10000000) (δ := 10423/1000000000) (ψ := -122331/1000000) 205 184
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t277 : ((-299440726277/5000000000000 : ℚ) : ℝ) ≤ stT205 277 := by
  have hc : ((-996737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).2
  have h0 : (0:ℝ) ≤ ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-299440726277/5000000000000 : ℚ) : ℝ)
      = ((300421/5000000 : ℚ) : ℝ) * ((-996737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c278 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-341051/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2901787/5000000) (δ := 10423/1000000000) (ψ := -122331/1000000) 205 184
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t278 : ((-51141020709/1250000000000 : ℚ) : ℝ) ≤ stT205 278 := by
  have hc : ((-85269/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).2
  have h0 : (0:ℝ) ≤ ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51141020709/1250000000000 : ℚ) : ℝ)
      = ((599761/10000000 : ℚ) : ℝ) * ((-85269/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c279 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-91/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -30964/78125) (δ := 257/25000000) (ψ := -122331/1000000) 205 184
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t279 : ((-174935757/200000000000 : ℚ) : ℝ) ≤ stT205 279 := by
  have hc : ((-1461/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).2
  have h0 : (0:ℝ) ≤ ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174935757/200000000000 : ℚ) : ℝ)
      = ((119737/2000000 : ℚ) : ℝ) * ((-1461/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c280 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((164641/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1064859/5000000) (δ := 10323/1000000000) (ψ := -122331/1000000) 205 184
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t280 : ((98384296399/2500000000000 : ℚ) : ℝ) ≤ stT205 280 := by
  have hc : ((329257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).1
  have hw2 : ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98384296399/2500000000000 : ℚ) : ℝ)
      = ((298807/5000000 : ℚ) : ℝ) * ((329257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c281 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((992681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4729/156250) (δ := 519/50000000) (ψ := -122331/1000000) 205 184
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t281 : ((592153030419/10000000000000 : ℚ) : ℝ) ≤ stT205 281 := by
  have hc : ((992631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).1
  have hw2 : ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((596549/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((592153030419/10000000000000 : ℚ) : ℝ)
      = ((596549/10000000 : ℚ) : ℝ) * ((992631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c282 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((41063/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1517949/10000000) (δ := 519/50000000) (ψ := -122331/1000000) 205 184
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t282 : ((48902316411/1000000000000 : ℚ) : ℝ) ≤ stT205 282 := by
  have hc : ((82121/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48902316411/1000000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((82121/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c283 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((117859/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3332097/10000000) (δ := 10323/1000000000) (ψ := -122331/1000000) 205 184
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t283 : ((17511251823/1250000000000 : ℚ) : ℝ) ≤ stT205 283 := by
  have hc : ((58917/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17511251823/1250000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((58917/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c284 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-466349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5139889/10000000) (δ := 519/50000000) (ψ := -122331/1000000) 205 184
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t284 : ((-276756969009/10000000000000 : ℚ) : ℝ) ≤ stT205 284 := by
  have hc : ((-466399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).2
  have h0 : (0:ℝ) ≤ ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-276756969009/10000000000000 : ℚ) : ℝ)
      = ((593391/10000000 : ℚ) : ℝ) * ((-466399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c285 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-467047/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1735319/2500000) (δ := 10423/1000000000) (ψ := -122331/1000000) 205 184
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t285 : ((-2161481501/39062500000 : ℚ) : ℝ) ≤ stT205 285 := by
  have hc : ((-14596/15625 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2161481501/39062500000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-14596/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c286 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-18767/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3485777/5000000) (δ := 10273/1000000000) (ψ := -122331/1000000) 205 185
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t286 : ((-693610149/12500000000 : ℚ) : ℝ) ≤ stT205 286 := by
  have hc : ((-1173/1250 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-693610149/12500000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-1173/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c287 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-481437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1295681/2500000) (δ := 10273/1000000000) (ψ := -122331/1000000) 205 185
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t287 : ((-142106554667/5000000000000 : ℚ) : ℝ) ≤ stT205 287 := by
  have hc : ((-481487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142106554667/5000000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-481487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c288 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((104591/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1700073/5000000) (δ := 1043/100000000) (ψ := -122331/1000000) 205 185
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t288 : ((6161603833/500000000000 : ℚ) : ℝ) ≤ stT205 288 := by
  have hc : ((52283/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6161603833/500000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((52283/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c289 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((398197/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1623719/10000000) (δ := 10273/1000000000) (ψ := -122331/1000000) 205 185
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t289 : ((11710935321/250000000000 : ℚ) : ℝ) ≤ stT205 289 := by
  have hc : ((99543/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11710935321/250000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((99543/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c290 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((998281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14661/1000000) (δ := 1033/100000000) (ψ := -122331/1000000) 205 185
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t290 : ((29309060391/500000000000 : ℚ) : ℝ) ≤ stT205 290 := by
  have hc : ((998231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29309060391/500000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((998231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c291 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((11279/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1910789/10000000) (δ := 1043/100000000) (ψ := -122331/1000000) 205 185
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t291 : ((21156494763/500000000000 : ℚ) : ℝ) ≤ stT205 291 := by
  have hc : ((360903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21156494763/500000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((360903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c292 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((4121/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3668971/10000000) (δ := 10273/1000000000) (ψ := -122331/1000000) 205 185
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t292 : ((482091879/80000000000 : ℚ) : ℝ) ≤ stT205 292 := by
  have hc : ((4119/40000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).1
  have hw2 : ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117041/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((482091879/80000000000 : ℚ) : ℝ)
      = ((117041/2000000 : ℚ) : ℝ) * ((4119/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c293 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-281349/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2710553/5000000) (δ := 10273/1000000000) (ψ := -122331/1000000) 205 185
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t293 : ((-82190330209/2500000000000 : ℚ) : ℝ) ≤ stT205 293 := by
  have hc : ((-140687/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).2
  have h0 : (0:ℝ) ≤ ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82190330209/2500000000000 : ℚ) : ℝ)
      = ((584207/10000000 : ℚ) : ℝ) * ((-140687/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c294 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-240627/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1433449/2000000) (δ := 1033/100000000) (ψ := -122331/1000000) 205 185
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t294 : ((-70171922037/1250000000000 : ℚ) : ℝ) ≤ stT205 294 := by
  have hc : ((-481279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70171922037/1250000000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-481279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c295 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-228129/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6800473/10000000) (δ := 10437/1000000000) (ψ := -122331/1000000) 205 186
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t295 : ((-265658457109/5000000000000 : ℚ) : ℝ) ≤ stT205 295 := by
  have hc : ((-456283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).2
  have h0 : (0:ℝ) ≤ ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-265658457109/5000000000000 : ℚ) : ℝ)
      = ((582223/10000000 : ℚ) : ℝ) * ((-456283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c296 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-27503/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2533061/5000000) (δ := 10337/1000000000) (ψ := -122331/1000000) 205 186
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t296 : ((-127901060711/5000000000000 : ℚ) : ℝ) ≤ stT205 296 := by
  have hc : ((-220049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).2
  have h0 : (0:ℝ) ≤ ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127901060711/5000000000000 : ℚ) : ℝ)
      = ((581239/10000000 : ℚ) : ℝ) * ((-220049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c297 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((233573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3337613/10000000) (δ := 10437/1000000000) (ψ := -122331/1000000) 205 186
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t297 : ((67751794467/5000000000000 : ℚ) : ℝ) ≤ stT205 297 := by
  have hc : ((233523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).1
  have hw2 : ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290129/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67751794467/5000000000000 : ℚ) : ℝ)
      = ((290129/5000000 : ℚ) : ℝ) * ((233523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c298 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((798511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1614947/10000000) (δ := 10337/1000000000) (ψ := -122331/1000000) 205 186
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t298 : ((115633920481/2500000000000 : ℚ) : ℝ) ≤ stT205 298 := by
  have hc : ((798461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115633920481/2500000000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((798461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c299 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((15612/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 101979/10000000) (δ := 5133/500000000) (ψ := -122331/1000000) 205 186
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t299 : ((144450981763/2500000000000 : ℚ) : ℝ) ≤ stT205 299 := by
  have hc : ((499559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).1
  have hw2 : ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((289157/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144450981763/2500000000000 : ℚ) : ℝ)
      = ((289157/5000000 : ℚ) : ℝ) * ((499559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c300 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((748323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 362633/2000000) (δ := 5183/500000000) (ψ := -122331/1000000) 205 186
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t300 : ((8640308331/200000000000 : ℚ) : ℝ) ≤ stT205 300 := by
  have hc : ((748273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8640308331/200000000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((748273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c301 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((81303/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3518663/10000000) (δ := 10337/1000000000) (ψ := -122331/1000000) 205 186
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t301 : ((2342391321/250000000000 : ℚ) : ℝ) ≤ stT205 301 := by
  have hc : ((40639/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).1
  have hw2 : ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57639/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2342391321/250000000000 : ℚ) : ℝ)
      = ((57639/1000000 : ℚ) : ℝ) * ((40639/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c302 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-246969/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5218523/10000000) (δ := 10337/1000000000) (ψ := -122331/1000000) 205 186
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t302 : ((-17766154923/625000000000 : ℚ) : ℝ) ≤ stT205 302 := by
  have hc : ((-123497/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17766154923/625000000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-123497/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c303 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-929959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1382549/2000000) (δ := 5183/500000000) (ψ := -122331/1000000) 205 186
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t303 : ((-106855244073/2000000000000 : ℚ) : ℝ) ≤ stT205 303 := by
  have hc : ((-930009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106855244073/2000000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-930009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c304 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-955643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3553291/5000000) (δ := 10359/1000000000) (ψ := -122331/1000000) 205 187
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t304 : ((-27406408161/500000000000 : ℚ) : ℝ) ≤ stT205 304 := by
  have hc : ((-955693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27406408161/500000000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-955693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c305 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-1127/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1355883/2500000) (δ := 10359/1000000000) (ψ := -122331/1000000) 205 187
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t305 : ((-6453763329/200000000000 : ℚ) : ℝ) ≤ stT205 305 := by
  have hc : ((-11271/20000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).2
  have h0 : (0:ℝ) ≤ ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6453763329/200000000000 : ℚ) : ℝ)
      = ((572599/10000000 : ℚ) : ℝ) * ((-11271/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c306 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((72367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1872957/5000000) (δ := 1293/125000000) (ψ := -122331/1000000) 205 187
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t306 : ((41340808537/10000000000000 : ℚ) : ℝ) ≤ stT205 306 := by
  have hc : ((72317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).1
  have hw2 : ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((571661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41340808537/10000000000000 : ℚ) : ℝ)
      = ((571661/10000000 : ℚ) : ℝ) * ((72317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c307 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((33761/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -259229/1250000) (δ := 10359/1000000000) (ψ := -122331/1000000) 205 187
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t307 : ((3853397741/100000000000 : ℚ) : ℝ) ≤ stT205 307 := by
  have hc : ((67517/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3853397741/100000000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((67517/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c308 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((493383/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -203591/5000000) (δ := 10359/1000000000) (ψ := -122331/1000000) 205 187
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t308 : ((70279093779/1250000000000 : ℚ) : ℝ) ≤ stT205 308 := by
  have hc : ((246679/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70279093779/1250000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((246679/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c309 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((438399/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1254087/10000000) (δ := 10259/1000000000) (ψ := -122331/1000000) 205 187
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t309 : ((1558638757/31250000000 : ℚ) : ℝ) ≤ stT205 309 := by
  have hc : ((219187/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1558638757/31250000000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((219187/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c310 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((197839/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 116399/400000) (δ := 2611/250000000) (ψ := -122331/1000000) 205 187
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t310 : ((56175318627/2500000000000 : ℚ) : ℝ) ≤ stT205 310 := by
  have hc : ((98907/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).1
  have hw2 : ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567961/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56175318627/2500000000000 : ℚ) : ℝ)
      = ((567961/10000000 : ℚ) : ℝ) * ((98907/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c311 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-250733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4560583/10000000) (δ := 10359/1000000000) (ψ := -122331/1000000) 205 187
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t311 : ((-17775749823/1250000000000 : ℚ) : ℝ) ≤ stT205 311 := by
  have hc : ((-250783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17775749823/1250000000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-250783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c312 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-790441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6205811/10000000) (δ := 1293/125000000) (ψ := -122331/1000000) 205 187
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t312 : ((-447527784249/10000000000000 : ℚ) : ℝ) ≤ stT205 312 := by
  have hc : ((-790491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-447527784249/10000000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-790491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c313 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-199999/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7845811/10000000) (δ := 1293/125000000) (ψ := -122331/1000000) 205 187
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t313 : ((-56525943553/1000000000000 : ℚ) : ℝ) ≤ stT205 313 := by
  have hc : ((-200009/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56525943553/1000000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-200009/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c314 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-49731/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -311369/500000) (δ := 2563/250000000) (ψ := -122331/1000000) 205 188
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t314 : ((-224532863709/5000000000000 : ℚ) : ℝ) ≤ stT205 314 := by
  have hc : ((-397873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).2
  have h0 : (0:ℝ) ≤ ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224532863709/5000000000000 : ℚ) : ℝ)
      = ((564333/10000000 : ℚ) : ℝ) * ((-397873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c315 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-265109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -574723/1250000) (δ := 647/62500000) (ψ := -122331/1000000) 205 188
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t315 : ((-149400391483/10000000000000 : ℚ) : ℝ) ≤ stT205 315 := by
  have hc : ((-265159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).2
  have h0 : (0:ℝ) ≤ ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149400391483/10000000000000 : ℚ) : ℝ)
      = ((563437/10000000 : ℚ) : ℝ) * ((-265159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c316 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((372267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -743341/2500000) (δ := 647/62500000) (ψ := -122331/1000000) 205 188
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t316 : ((209388067831/10000000000000 : ℚ) : ℝ) ≤ stT205 316 := by
  have hc : ((372217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209388067831/10000000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((372217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c317 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((42843/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33853/250000) (δ := 2563/250000000) (ψ := -122331/1000000) 205 188
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t317 : ((9624632411/200000000000 : ℚ) : ℝ) ≤ stT205 317 := by
  have hc : ((85681/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).1
  have hw2 : ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((112331/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9624632411/200000000000 : ℚ) : ℝ)
      = ((112331/2000000 : ℚ) : ℝ) * ((85681/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c318 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((198919/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5201/200000) (δ := 2563/250000000) (ψ := -122331/1000000) 205 188
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t318 : ((27885649437/500000000000 : ℚ) : ℝ) ≤ stT205 318 := by
  have hc : ((198909/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).1
  have hw2 : ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140193/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27885649437/500000000000 : ℚ) : ℝ)
      = ((140193/2500000 : ℚ) : ℝ) * ((198909/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c319 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((733269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 934599/5000000) (δ := 10451/1000000000) (ψ := -122331/1000000) 205 188
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t319 : ((102630863087/2500000000000 : ℚ) : ℝ) ≤ stT205 319 := by
  have hc : ((733219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).1
  have hw2 : ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((139973/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102630863087/2500000000000 : ℚ) : ℝ)
      = ((139973/2500000 : ℚ) : ℝ) * ((733219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c320 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((180513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 173661/500000) (δ := 2563/250000000) (ψ := -122331/1000000) 205 188
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t320 : ((12610213051/1250000000000 : ℚ) : ℝ) ≤ stT205 320 := by
  have hc : ((180463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).1
  have hw2 : ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69877/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12610213051/1250000000000 : ℚ) : ℝ)
      = ((69877/1250000 : ℚ) : ℝ) * ((180463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c321 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-221137/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5072323/10000000) (δ := 10451/1000000000) (ψ := -122331/1000000) 205 188
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t321 : ((-30860171413/1250000000000 : ℚ) : ℝ) ≤ stT205 321 := by
  have hc : ((-110581/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30860171413/1250000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-110581/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c322 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-444639/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6666403/10000000) (δ := 10451/1000000000) (ψ := -122331/1000000) 205 188
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t322 : ((-30975238657/625000000000 : ℚ) : ℝ) ≤ stT205 322 := by
  have hc : ((-55583/62500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).2
  have h0 : (0:ℝ) ≤ ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30975238657/625000000000 : ℚ) : ℝ)
      = ((557279/10000000 : ℚ) : ℝ) * ((-55583/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c323 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-493563/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7452401/10000000) (δ := 2069/200000000) (ψ := -122331/1000000) 205 189
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t323 : ((-13731988351/250000000000 : ℚ) : ℝ) ≤ stT205 323 := by
  have hc : ((-123397/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).2
  have h0 : (0:ℝ) ≤ ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13731988351/250000000000 : ℚ) : ℝ)
      = ((111283/2000000 : ℚ) : ℝ) * ((-123397/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c324 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-175191/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5868161/10000000) (δ := 2069/200000000) (ψ := -122331/1000000) 205 189
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t324 : ((-48667677823/1250000000000 : ℚ) : ℝ) ≤ stT205 324 := by
  have hc : ((-350407/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).2
  have h0 : (0:ℝ) ≤ ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48667677823/1250000000000 : ℚ) : ℝ)
      = ((138889/2500000 : ℚ) : ℝ) * ((-350407/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c325 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-28847/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4288841/10000000) (δ := 2069/200000000) (ψ := -122331/1000000) 205 189
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t325 : ((-16007006757/2000000000000 : ℚ) : ℝ) ≤ stT205 325 := by
  have hc : ((-28857/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).2
  have h0 : (0:ℝ) ≤ ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16007006757/2000000000000 : ℚ) : ℝ)
      = ((554701/10000000 : ℚ) : ℝ) * ((-28857/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c326 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((233131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1357169/5000000) (δ := 5179/500000000) (ψ := -122331/1000000) 205 189
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t326 : ((8069080743/312500000000 : ℚ) : ℝ) ≤ stT205 326 := by
  have hc : ((116553/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).1
  have hw2 : ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69231/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8069080743/312500000000 : ℚ) : ℝ)
      = ((69231/1250000 : ℚ) : ℝ) * ((116553/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c327 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((897/1000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1144653/10000000) (δ := 5179/500000000) (ψ := -122331/1000000) 205 189
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t327 : ((9920284939/200000000000 : ℚ) : ℝ) ≤ stT205 327 := by
  have hc : ((17939/20000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).1
  have hw2 : ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((553001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9920284939/200000000000 : ℚ) : ℝ)
      = ((553001/10000000 : ℚ) : ℝ) * ((17939/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c328 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((985903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 84053/2000000) (δ := 2089/200000000) (ψ := -122331/1000000) 205 189
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t328 : ((544345634921/10000000000000 : ℚ) : ℝ) ≤ stT205 328 := by
  have hc : ((985853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).1
  have hw2 : ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((552157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((544345634921/10000000000000 : ℚ) : ℝ)
      = ((552157/10000000 : ℚ) : ℝ) * ((985853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c329 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((702319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1980367/10000000) (δ := 5179/500000000) (ψ := -122331/1000000) 205 189
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t329 : ((387172838273/10000000000000 : ℚ) : ℝ) ≤ stT205 329 := by
  have hc : ((702269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).1
  have hw2 : ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((551317/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((387172838273/10000000000000 : ℚ) : ℝ)
      = ((551317/10000000 : ℚ) : ℝ) * ((702269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c330 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((155857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3535753/10000000) (δ := 5129/500000000) (ψ := -122331/1000000) 205 189
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t330 : ((85768793167/10000000000000 : ℚ) : ℝ) ≤ stT205 330 := by
  have hc : ((155807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).1
  have hw2 : ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((550481/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85768793167/10000000000000 : ℚ) : ℝ)
      = ((550481/10000000 : ℚ) : ℝ) * ((155807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c331 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-223663/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 635803/1250000) (δ := 2069/200000000) (ψ := -122331/1000000) 205 189
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t331 : ((-307375273/12500000000 : ℚ) : ℝ) ≤ stT205 331 := by
  have hc : ((-27961/62500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-307375273/12500000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-27961/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c332 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-441491/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 414527/625000) (δ := 5179/500000000) (ψ := -122331/1000000) 205 189
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t332 : ((-30289211769/625000000000 : ℚ) : ℝ) ≤ stT205 332 := by
  have hc : ((-110379/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).2
  have h0 : (0:ℝ) ≤ ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30289211769/625000000000 : ℚ) : ℝ)
      = ((274411/5000000 : ℚ) : ℝ) * ((-110379/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c333 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-99183/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1883547/2500000) (δ := 10337/1000000000) (ψ := -122331/1000000) 205 190
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t333 : ((-13588681609/250000000000 : ℚ) : ℝ) ≤ stT205 333 := by
  have hc : ((-24797/25000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).2
  have h0 : (0:ℝ) ≤ ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13588681609/250000000000 : ℚ) : ℝ)
      = ((547997/10000000 : ℚ) : ℝ) * ((-24797/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c334 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-368353/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5997457/10000000) (δ := 10437/1000000000) (ψ := -122331/1000000) 205 190
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t334 : ((-12597975033/312500000000 : ℚ) : ℝ) ≤ stT205 334 := by
  have hc : ((-184189/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).2
  have h0 : (0:ℝ) ≤ ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12597975033/312500000000 : ℚ) : ℝ)
      = ((68397/1250000 : ℚ) : ℝ) * ((-184189/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c335 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-213659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4465287/10000000) (δ := 10437/1000000000) (ψ := -122331/1000000) 205 190
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t335 : ((-116761835531/10000000000000 : ℚ) : ℝ) ≤ stT205 335 := by
  have hc : ((-213709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).2
  have h0 : (0:ℝ) ≤ ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116761835531/10000000000000 : ℚ) : ℝ)
      = ((546359/10000000 : ℚ) : ℝ) * ((-213709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c336 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((385459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2937729/10000000) (δ := 5133/500000000) (ψ := -122331/1000000) 205 190
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t336 : ((26282195937/1250000000000 : ℚ) : ℝ) ≤ stT205 336 := by
  have hc : ((385409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26282195937/1250000000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((385409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c337 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((844121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -707341/5000000) (δ := 10437/1000000000) (ψ := -122331/1000000) 205 190
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t337 : ((229897086057/5000000000000 : ℚ) : ℝ) ≤ stT205 337 := by
  have hc : ((844071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).1
  have hw2 : ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((272367/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229897086057/5000000000000 : ℚ) : ℝ)
      = ((272367/5000000 : ℚ) : ℝ) * ((844071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c338 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((499569/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 20761/2000000) (δ := 5183/500000000) (ψ := -122331/1000000) 205 190
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t338 : ((4245562013/78125000000 : ℚ) : ℝ) ≤ stT205 338 := by
  have hc : ((62443/62500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).1
  have hw2 : ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67991/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4245562013/78125000000 : ℚ) : ℝ)
      = ((67991/1250000 : ℚ) : ℝ) * ((62443/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c339 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((797803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1617883/10000000) (δ := 10437/1000000000) (ψ := -122331/1000000) 205 190
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t339 : ((693247357/16000000000 : ℚ) : ℝ) ≤ stT205 339 := by
  have hc : ((797753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).1
  have hw2 : ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((869/16000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((693247357/16000000000 : ℚ) : ℝ)
      = ((869/16000 : ℚ) : ℝ) * ((797753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c340 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((314391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 781863/2500000) (δ := 10337/1000000000) (ψ := -122331/1000000) 205 190
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t340 : ((85237648583/5000000000000 : ℚ) : ℝ) ≤ stT205 340 := by
  have hc : ((314341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).1
  have hw2 : ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85237648583/5000000000000 : ℚ) : ℝ)
      = ((271163/5000000 : ℚ) : ℝ) * ((314341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c341 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-278497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2316281/5000000) (δ := 10337/1000000000) (ψ := -122331/1000000) 205 190
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t341 : ((-150841835457/10000000000000 : ℚ) : ℝ) ≤ stT205 341 := by
  have hc : ((-278547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).2
  have h0 : (0:ℝ) ≤ ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-150841835457/10000000000000 : ℚ) : ℝ)
      = ((541531/10000000 : ℚ) : ℝ) * ((-278547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c342 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-193087/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1533329/2500000) (δ := 5133/500000000) (ψ := -122331/1000000) 205 190
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t342 : ((-208832861061/5000000000000 : ℚ) : ℝ) ≤ stT205 342 := by
  have hc : ((-386199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-208832861061/5000000000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-386199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c343 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-995977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3814831/5000000) (δ := 10337/1000000000) (ψ := -122331/1000000) 205 190
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t343 : ((-10756095573/200000000000 : ℚ) : ℝ) ≤ stT205 343 := by
  have hc : ((-996027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).2
  have h0 : (0:ℝ) ≤ ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10756095573/200000000000 : ℚ) : ℝ)
      = ((10799/200000 : ℚ) : ℝ) * ((-996027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c344 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-218543/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6586311/10000000) (δ := 10273/1000000000) (ψ := -122331/1000000) 205 191
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t344 : ((-58918628801/1250000000000 : ℚ) : ℝ) ≤ stT205 344 := by
  have hc : ((-437111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).2
  have h0 : (0:ℝ) ≤ ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58918628801/1250000000000 : ℚ) : ℝ)
      = ((134791/2500000 : ℚ) : ℝ) * ((-437111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c345 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-225843/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2549313/5000000) (δ := 10273/1000000000) (ψ := -122331/1000000) 205 191
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t345 : ((-15200408197/625000000000 : ℚ) : ℝ) ≤ stT205 345 := by
  have hc : ((-56467/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).2
  have h0 : (0:ℝ) ≤ ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15200408197/625000000000 : ℚ) : ℝ)
      = ((269191/5000000 : ℚ) : ℝ) * ((-56467/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c346 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((24871/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3615297/10000000) (δ := 10373/1000000000) (ψ := -122331/1000000) 205 191
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t346 : ((13365348183/2000000000000 : ℚ) : ℝ) ≤ stT205 346 := by
  have hc : ((24861/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13365348183/2000000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((24861/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c347 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((164151/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1068111/5000000) (δ := 10373/1000000000) (ψ := -122331/1000000) 205 191
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t347 : ((44057071339/1250000000000 : ℚ) : ℝ) ≤ stT205 347 := by
  have hc : ((328277/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44057071339/1250000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((328277/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c348 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((120651/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -661401/10000000) (δ := 10273/1000000000) (ψ := -122331/1000000) 205 191
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t348 : ((32336171053/625000000000 : ℚ) : ℝ) ≤ stT205 348 := by
  have hc : ((482579/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).1
  have hw2 : ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32336171053/625000000000 : ℚ) : ℝ)
      = ((67007/1250000 : ℚ) : ℝ) * ((482579/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c349 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((948069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 404609/5000000) (δ := 10373/1000000000) (ψ := -122331/1000000) 205 191
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t349 : ((507462246453/10000000000000 : ℚ) : ℝ) ≤ stT205 349 := by
  have hc : ((948019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).1
  have hw2 : ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((535287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((507462246453/10000000000000 : ℚ) : ℝ)
      = ((535287/10000000 : ℚ) : ℝ) * ((948019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c350 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((306781/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2275583/10000000) (δ := 10373/1000000000) (ψ := -122331/1000000) 205 191
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t350 : ((20495978829/625000000000 : ℚ) : ℝ) ≤ stT205 350 := by
  have hc : ((76689/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).1
  have hw2 : ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((267261/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20495978829/625000000000 : ℚ) : ℝ)
      = ((267261/5000000 : ℚ) : ℝ) * ((76689/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c351 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((37803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 934449/2500000) (δ := 1043/100000000) (ψ := -122331/1000000) 205 191
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t351 : ((7876713/1953125000 : ℚ) : ℝ) ≤ stT205 351 := by
  have hc : ((18889/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).1
  have hw2 : ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((834/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7876713/1953125000 : ℚ) : ℝ)
      = ((834/15625 : ℚ) : ℝ) * ((18889/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c352 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-486017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 162369/312500) (δ := 10373/1000000000) (ψ := -122331/1000000) 205 191
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t352 : ((-129537341567/5000000000000 : ℚ) : ℝ) ≤ stT205 352 := by
  have hc : ((-486067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129537341567/5000000000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-486067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c353 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-443103/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6649719/10000000) (δ := 10273/1000000000) (ψ := -122331/1000000) 205 191
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t353 : ((-29481693577/625000000000 : ℚ) : ℝ) ≤ stT205 353 := by
  have hc : ((-55391/62500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).2
  have h0 : (0:ℝ) ≤ ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29481693577/625000000000 : ℚ) : ℝ)
      = ((532247/10000000 : ℚ) : ℝ) * ((-55391/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c354 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-49759/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7608433/10000000) (δ := 257/25000000) (ψ := -122331/1000000) 205 192
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t354 : ((-10579195377/200000000000 : ℚ) : ℝ) ≤ stT205 354 := by
  have hc : ((-99523/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).2
  have h0 : (0:ℝ) ≤ ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10579195377/200000000000 : ℚ) : ℝ)
      = ((106299/2000000 : ℚ) : ℝ) * ((-99523/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c355 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-779779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6162773/10000000) (δ := 257/25000000) (ψ := -122331/1000000) 205 192
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t355 : ((-82778068521/2000000000000 : ℚ) : ℝ) ≤ stT205 355 := by
  have hc : ((-779829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82778068521/2000000000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-779829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c356 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-312333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4721111/10000000) (δ := 10423/1000000000) (ψ := -122331/1000000) 205 192
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t356 : ((-165562677617/10000000000000 : ℚ) : ℝ) ≤ stT205 356 := by
  have hc : ((-312383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).2
  have h0 : (0:ℝ) ≤ ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165562677617/10000000000000 : ℚ) : ℝ)
      = ((529999/10000000 : ℚ) : ℝ) * ((-312383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c357 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((50909/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -820887/2500000) (δ := 257/25000000) (ψ := -122331/1000000) 205 192
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t357 : ((3367325143/250000000000 : ℚ) : ℝ) ≤ stT205 357 := by
  have hc : ((50899/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).1
  have hw2 : ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66157/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3367325143/250000000000 : ℚ) : ℝ)
      = ((66157/1250000 : ℚ) : ℝ) * ((50899/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c358 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((738473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1849983/10000000) (δ := 257/25000000) (ψ := -122331/1000000) 205 192
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t358 : ((97567092567/2500000000000 : ℚ) : ℝ) ≤ stT205 358 := by
  have hc : ((738423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).1
  have hw2 : ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((132129/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97567092567/2500000000000 : ℚ) : ℝ)
      = ((132129/2500000 : ℚ) : ℝ) * ((738423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c359 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((985893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6569/156250) (δ := 10423/1000000000) (ψ := -122331/1000000) 205 192
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t359 : ((520307232697/10000000000000 : ℚ) : ℝ) ≤ stT205 359 := by
  have hc : ((985843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((520307232697/10000000000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((985843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c360 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((115031/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 502603/5000000) (δ := 519/50000000) (ψ := -122331/1000000) 205 192
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t360 : ((121246668777/2500000000000 : ℚ) : ℝ) ≤ stT205 360 := by
  have hc : ((460099/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).1
  have hw2 : ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121246668777/2500000000000 : ℚ) : ℝ)
      = ((263523/5000000 : ℚ) : ℝ) * ((460099/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c361 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((70587/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2426829/10000000) (δ := 10423/1000000000) (ψ := -122331/1000000) 205 192
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t361 : ((29718165949/1000000000000 : ℚ) : ℝ) ≤ stT205 361 := by
  have hc : ((282323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29718165949/1000000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((282323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c362 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((32967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1922279/5000000) (δ := 10323/1000000000) (ψ := -122331/1000000) 205 192
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t362 : ((4325195049/2500000000000 : ℚ) : ℝ) ≤ stT205 362 := by
  have hc : ((32917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4325195049/2500000000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((32917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c363 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-507723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5258341/10000000) (δ := 519/50000000) (ψ := -122331/1000000) 205 192
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t363 : ((-4164246373/156250000000 : ℚ) : ℝ) ≤ stT205 363 := by
  have hc : ((-507773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4164246373/156250000000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-507773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c364 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-222403/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1667057/2500000) (δ := 10323/1000000000) (ψ := -122331/1000000) 205 192
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t364 : ((-233155054833/5000000000000 : ℚ) : ℝ) ≤ stT205 364 := by
  have hc : ((-444831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233155054833/5000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-444831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c365 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-24903/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7633691/10000000) (δ := 10387/1000000000) (ψ := -122331/1000000) 205 193
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t365 : ((-1629435269/31250000000 : ℚ) : ℝ) ≤ stT205 365 := by
  have hc : ((-99617/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1629435269/31250000000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-99617/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c366 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-796691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6231491/10000000) (δ := 10387/1000000000) (ψ := -122331/1000000) 205 193
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t366 : ((-416463691369/10000000000000 : ℚ) : ℝ) ≤ stT205 366 := by
  have hc : ((-796741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-416463691369/10000000000000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-796741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c367 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-354573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -966627/2000000) (δ := 10287/1000000000) (ψ := -122331/1000000) 205 193
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t367 : ((-46277946877/2500000000000 : ℚ) : ℝ) ≤ stT205 367 := by
  have hc : ((-354623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46277946877/2500000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-354623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c368 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((194127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3438571/10000000) (δ := 10387/1000000000) (ψ := -122331/1000000) 205 193
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t368 : ((50584811511/5000000000000 : ℚ) : ℝ) ≤ stT205 368 := by
  have hc : ((194077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50584811511/5000000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((194077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c369 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((42679/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10239/50000) (δ := 10287/1000000000) (ψ := -122331/1000000) 205 193
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t369 : ((177729314653/5000000000000 : ℚ) : ℝ) ≤ stT205 369 := by
  have hc : ((341407/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177729314653/5000000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((341407/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c370 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((482637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -66077/1000000) (δ := 10287/1000000000) (ψ := -122331/1000000) 205 193
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t370 : ((501795827/10000000000 : ℚ) : ℝ) ≤ stT205 370 := by
  have hc : ((120653/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).1
  have hw2 : ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((4159/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((501795827/10000000000 : ℚ) : ℝ)
      = ((4159/80000 : ℚ) : ℝ) * ((120653/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c371 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((958533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 722467/10000000) (δ := 651/62500000) (ψ := -122331/1000000) 205 193
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t371 : ((248809726521/5000000000000 : ℚ) : ℝ) ≤ stT205 371 := by
  have hc : ((958483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).1
  have hw2 : ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((259587/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((248809726521/5000000000000 : ℚ) : ℝ)
      = ((259587/5000000 : ℚ) : ℝ) * ((958483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c372 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((333431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 420403/2000000) (δ := 10287/1000000000) (ψ := -122331/1000000) 205 193
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t372 : ((3457253517/100000000000 : ℚ) : ℝ) ≤ stT205 372 := by
  have hc : ((166703/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).1
  have hw2 : ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((20739/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3457253517/100000000000 : ℚ) : ℝ)
      = ((20739/400000 : ℚ) : ℝ) * ((166703/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c373 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((178683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 217367/625000) (δ := 651/62500000) (ψ := -122331/1000000) 205 193
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t373 : ((4624629737/500000000000 : ℚ) : ℝ) ≤ stT205 373 := by
  have hc : ((178633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).1
  have hw2 : ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25889/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4624629737/500000000000 : ℚ) : ℝ)
      = ((25889/500000 : ℚ) : ℝ) * ((178633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c374 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-360869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4849989/10000000) (δ := 10387/1000000000) (ψ := -122331/1000000) 205 193
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t374 : ((-5832090121/312500000000 : ℚ) : ℝ) ≤ stT205 374 := by
  have hc : ((-360919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5832090121/312500000000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-360919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c375 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-99193/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6218517/10000000) (δ := 651/62500000) (ψ := -122331/1000000) 205 193
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t375 : ((-102452588603/2500000000000 : ℚ) : ℝ) ≤ stT205 375 := by
  have hc : ((-396797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).2
  have h0 : (0:ℝ) ≤ ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102452588603/2500000000000 : ℚ) : ℝ)
      = ((258199/5000000 : ℚ) : ℝ) * ((-396797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c376 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-994147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1895839/2500000) (δ := 2579/250000000) (ψ := -122331/1000000) 205 193
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t376 : ((-512718329067/10000000000000 : ℚ) : ℝ) ≤ stT205 376 := by
  have hc : ((-994197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).2
  have h0 : (0:ℝ) ≤ ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512718329067/10000000000000 : ℚ) : ℝ)
      = ((515711/10000000 : ℚ) : ℝ) * ((-994197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c377 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-906351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6763407/10000000) (δ := 5147/500000000) (ψ := -122331/1000000) 205 194
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t377 : ((-466820987827/10000000000000 : ℚ) : ℝ) ≤ stT205 377 := by
  have hc : ((-906401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).2
  have h0 : (0:ℝ) ≤ ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-466820987827/10000000000000 : ℚ) : ℝ)
      = ((515027/10000000 : ℚ) : ℝ) * ((-906401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c378 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-4461/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1081159/2000000) (δ := 10409/1000000000) (ψ := -122331/1000000) 205 194
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t378 : ((-2294698783/80000000000 : ℚ) : ℝ) ≤ stT205 378 := by
  have hc : ((-22307/40000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).2
  have h0 : (0:ℝ) ≤ ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2294698783/80000000000 : ℚ) : ℝ)
      = ((102869/2000000 : ℚ) : ℝ) * ((-22307/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c379 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-4987/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2025859/5000000) (δ := 5197/500000000) (ψ := -122331/1000000) 205 194
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t379 : ((-10016487/3906250000 : ℚ) : ℝ) ≤ stT205 379 := by
  have hc : ((-156/3125 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10016487/3906250000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-156/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c380 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((117719/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2701281/10000000) (δ := 10309/1000000000) (ψ := -122331/1000000) 205 194
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t380 : ((120764279457/5000000000000 : ℚ) : ℝ) ≤ stT205 380 := by
  have hc : ((235413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).1
  have hw2 : ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120764279457/5000000000000 : ℚ) : ℝ)
      = ((512989/10000000 : ℚ) : ℝ) * ((235413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c381 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((856807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -67719/500000) (δ := 10409/1000000000) (ψ := -122331/1000000) 205 194
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t381 : ((87785892491/2000000000000 : ℚ) : ℝ) ≤ stT205 381 := by
  have hc : ((856757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).1
  have hw2 : ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102463/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87785892491/2000000000000 : ℚ) : ℝ)
      = ((102463/2000000 : ℚ) : ℝ) * ((856757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c382 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((99999/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10963/10000000) (δ := 5197/500000000) (ψ := -122331/1000000) 205 194
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t382 : ((6395166267/125000000000 : ℚ) : ℝ) ≤ stT205 382 := by
  have hc : ((49997/50000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6395166267/125000000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((49997/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c383 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((107753/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 265773/2000000) (δ := 10409/1000000000) (ψ := -122331/1000000) 205 194
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t383 : ((215062513/4882812500 : ℚ) : ℝ) ≤ stT205 383 := by
  have hc : ((430987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215062513/4882812500 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((430987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c384 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((241769/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 133263/500000) (δ := 10409/1000000000) (ψ := -122331/1000000) 205 194
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t384 : ((771027379/31250000000 : ℚ) : ℝ) ≤ stT205 384 := by
  have hc : ((15109/31250 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).1
  have hw2 : ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((771027379/31250000000 : ℚ) : ℝ)
      = ((51031/1000000 : ℚ) : ℝ) * ((15109/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c385 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-7117/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 399817/1000000) (δ := 10409/1000000000) (ψ := -122331/1000000) 205 194
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t385 : ((-454191927/312500000000 : ℚ) : ℝ) ≤ stT205 385 := by
  have hc : ((-14259/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).2
  have h0 : (0:ℝ) ≤ ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-454191927/312500000000 : ℚ) : ℝ)
      = ((31853/625000 : ℚ) : ℝ) * ((-14259/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c386 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-531391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1065519/2000000) (δ := 10409/1000000000) (ψ := -122331/1000000) 205 194
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t386 : ((-270496560267/10000000000000 : ℚ) : ℝ) ≤ stT205 386 := by
  have hc : ((-531441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-270496560267/10000000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-531441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c387 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-443461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6653587/10000000) (δ := 5197/500000000) (ψ := -122331/1000000) 205 194
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t387 : ((-112718397447/2500000000000 : ℚ) : ℝ) ≤ stT205 387 := by
  have hc : ((-221743/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112718397447/2500000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-221743/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c388 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-199761/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -966471/1250000) (δ := 10301/1000000000) (ψ := -122331/1000000) 205 195
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t388 : ((-50709271327/1000000000000 : ℚ) : ℝ) ≤ stT205 388 := by
  have hc : ((-199771/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).2
  have h0 : (0:ℝ) ≤ ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50709271327/1000000000000 : ℚ) : ℝ)
      = ((253837/5000000 : ℚ) : ℝ) * ((-199771/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c389 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-167669/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6412593/10000000) (δ := 10301/1000000000) (ψ := -122331/1000000) 205 195
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t389 : ((-85016774259/2000000000000 : ℚ) : ℝ) ≤ stT205 389 := by
  have hc : ((-167679/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85016774259/2000000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-167679/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c390 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-225517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6371/12500) (δ := 5201/500000000) (ψ := -122331/1000000) 205 195
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t390 : ((-5710385127/250000000000 : ℚ) : ℝ) ≤ stT205 390 := by
  have hc : ((-112771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).2
  have h0 : (0:ℝ) ≤ ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5710385127/250000000000 : ℚ) : ℝ)
      = ((50637/1000000 : ℚ) : ℝ) * ((-112771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c391 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((57009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -378439/1000000) (δ := 5201/500000000) (ψ := -122331/1000000) 205 195
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t391 : ((28805362439/10000000000000 : ℚ) : ℝ) ≤ stT205 391 := by
  have hc : ((56959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28805362439/10000000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((56959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c392 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((274293/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -154707/625000) (δ := 10401/1000000000) (ψ := -122331/1000000) 205 195
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t392 : ((8657886523/312500000000 : ℚ) : ℝ) ≤ stT205 392 := by
  have hc : ((68567/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8657886523/312500000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((68567/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c393 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((892551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -292391/2500000) (δ := 5151/500000000) (ψ := -122331/1000000) 205 195
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t393 : ((450206956933/10000000000000 : ℚ) : ℝ) ≤ stT205 393 := by
  have hc : ((892501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((450206956933/10000000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((892501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c394 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((249647/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33213/2500000) (δ := 10301/1000000000) (ψ := -122331/1000000) 205 195
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t394 : ((15720483003/312500000000 : ℚ) : ℝ) ≤ stT205 394 := by
  have hc : ((499269/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).1
  have hw2 : ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31487/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15720483003/312500000000 : ℚ) : ℝ)
      = ((31487/625000 : ℚ) : ℝ) * ((499269/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c395 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((2101/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1431937/10000000) (δ := 10301/1000000000) (ψ := -122331/1000000) 205 195
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t395 : ((4228254639/100000000000 : ℚ) : ℝ) ≤ stT205 395 := by
  have hc : ((16807/20000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).1
  have hw2 : ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4228254639/100000000000 : ℚ) : ℝ)
      = ((251577/5000000 : ℚ) : ℝ) * ((16807/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c396 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((92299/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2727793/10000000) (δ := 10401/1000000000) (ψ := -122331/1000000) 205 195
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t396 : ((23188441851/1000000000000 : ℚ) : ℝ) ≤ stT205 396 := by
  have hc : ((92289/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).1
  have hw2 : ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251259/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23188441851/1000000000000 : ℚ) : ℝ)
      = ((251259/5000000 : ℚ) : ℝ) * ((92289/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c397 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-18661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2010159/5000000) (δ := 10401/1000000000) (ψ := -122331/1000000) 205 195
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t397 : ((-2344560449/1250000000000 : ℚ) : ℝ) ≤ stT205 397 := by
  have hc : ((-9343/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2344560449/1250000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-9343/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c398 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-262651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2654833/5000000) (δ := 5151/500000000) (ψ := -122331/1000000) 205 195
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t398 : ((-6583382919/250000000000 : ℚ) : ℝ) ≤ stT205 398 := by
  have hc : ((-65669/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).2
  have h0 : (0:ℝ) ≤ ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6583382919/250000000000 : ℚ) : ℝ)
      = ((100251/2000000 : ℚ) : ℝ) * ((-65669/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c399 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-218999/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6595733/10000000) (δ := 10401/1000000000) (ψ := -122331/1000000) 205 195
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t399 : ((-219286140421/5000000000000 : ℚ) : ℝ) ≤ stT205 399 := by
  have hc : ((-438023/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).2
  have h0 : (0:ℝ) ≤ ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219286140421/5000000000000 : ℚ) : ℝ)
      = ((500627/10000000 : ℚ) : ℝ) * ((-438023/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c400 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-62497/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7829391/10000000) (δ := 10309/1000000000) (ψ := -122331/1000000) 205 196
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t400 : ((-250001000001/5000000000000 : ℚ) : ℝ) ≤ stT205 400 := by
  have hc : ((-500001/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250001000001/5000000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-500001/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c401 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-866973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -654973/1000000) (δ := 5147/500000000) (ψ := -122331/1000000) 205 196
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t401 : ((-432971344671/10000000000000 : ℚ) : ℝ) ≤ stT205 401 := by
  have hc : ((-867023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).2
  have h0 : (0:ℝ) ≤ ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-432971344671/10000000000000 : ℚ) : ℝ)
      = ((499377/10000000 : ℚ) : ℝ) * ((-867023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c402 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-128217/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5273297/10000000) (δ := 10409/1000000000) (ψ := -122331/1000000) 205 196
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t402 : ((-25582041709/1000000000000 : ℚ) : ℝ) ≤ stT205 402 := by
  have hc : ((-256459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).2
  have h0 : (0:ℝ) ≤ ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25582041709/1000000000000 : ℚ) : ℝ)
      = ((99751/2000000 : ℚ) : ℝ) * ((-256459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c403 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-7299/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3999991/10000000) (δ := 10309/1000000000) (ψ := -122331/1000000) 205 196
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t403 : ((-910530341/625000000000 : ℚ) : ℝ) ≤ stT205 403 := by
  have hc : ((-14623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-910530341/625000000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-14623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c404 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((11519/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1364931/5000000) (δ := 10409/1000000000) (ψ := -122331/1000000) 205 196
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t404 : ((11460575889/500000000000 : ℚ) : ℝ) ≤ stT205 404 := by
  have hc : ((46071/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).1
  have hw2 : ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((248759/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11460575889/500000000000 : ℚ) : ℝ)
      = ((248759/5000000 : ℚ) : ℝ) * ((46071/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c405 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((833633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -73143/500000) (δ := 5147/500000000) (ψ := -122331/1000000) 205 196
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t405 : ((414209893449/10000000000000 : ℚ) : ℝ) ≤ stT205 405 := by
  have hc : ((833583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((414209893449/10000000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((833583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c406 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((498417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24873/1250000) (δ := 5197/500000000) (ψ := -122331/1000000) 205 196
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t406 : ((30918433009/625000000000 : ℚ) : ℝ) ≤ stT205 406 := by
  have hc : ((62299/62500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30918433009/625000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((62299/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c407 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((22779/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 530883/5000000) (δ := 5197/500000000) (ψ := -122331/1000000) 205 196
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t407 : ((45161991591/1000000000000 : ℚ) : ℝ) ≤ stT205 407 := by
  have hc : ((91111/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45161991591/1000000000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((91111/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c408 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((119923/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2319441/10000000) (δ := 5197/500000000) (ψ := -122331/1000000) 205 196
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t408 : ((59365688649/2000000000000 : ℚ) : ℝ) ≤ stT205 408 := by
  have hc : ((119913/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59365688649/2000000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((119913/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c409 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((140711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3574041/10000000) (δ := 5197/500000000) (ψ := -122331/1000000) 205 196
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t409 : ((17388090837/2500000000000 : ℚ) : ℝ) ≤ stT205 409 := by
  have hc : ((140661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17388090837/2500000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((140661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c410 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-351741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2412783/5000000) (δ := 5197/500000000) (ψ := -122331/1000000) 205 196
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t410 : ((-34747452443/2000000000000 : ℚ) : ℝ) ≤ stT205 410 := by
  have hc : ((-351791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).2
  have h0 : (0:ℝ) ≤ ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34747452443/2000000000000 : ℚ) : ℝ)
      = ((98773/2000000 : ℚ) : ℝ) * ((-351791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c411 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-757079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1518517/2500000) (δ := 10409/1000000000) (ψ := -122331/1000000) 205 196
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t411 : ((-23341529941/625000000000 : ℚ) : ℝ) ≤ stT205 411 := by
  have hc : ((-757129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23341529941/625000000000 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-757129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c412 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-977233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3659747/5000000) (δ := 10309/1000000000) (ψ := -122331/1000000) 205 196
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t412 : ((-96294625839/2000000000000 : ℚ) : ℝ) ≤ stT205 412 := by
  have hc : ((-977283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).2
  have h0 : (0:ℝ) ≤ ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96294625839/2000000000000 : ℚ) : ℝ)
      = ((98533/2000000 : ℚ) : ℝ) * ((-977283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c413 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-60011/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7146067/10000000) (δ := 10287/1000000000) (ψ := -122331/1000000) 205 197
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t413 : ((-59062060921/1250000000000 : ℚ) : ℝ) ≤ stT205 413 := by
  have hc : ((-480113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59062060921/1250000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-480113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c414 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-35583/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5906637/10000000) (δ := 10287/1000000000) (ψ := -122331/1000000) 205 197
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t414 : ((-17489348027/500000000000 : ℚ) : ℝ) ≤ stT205 414 := by
  have hc : ((-71171/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17489348027/500000000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-71171/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c415 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-73229/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4670179/10000000) (δ := 651/62500000) (ψ := -122331/1000000) 205 197
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t415 : ((-71905721523/5000000000000 : ℚ) : ℝ) ≤ stT205 415 := by
  have hc : ((-146483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71905721523/5000000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-146483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c416 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((48711/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1718373/5000000) (δ := 10387/1000000000) (ψ := -122331/1000000) 205 197
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t416 : ((4775277513/500000000000 : ℚ) : ℝ) ≤ stT205 416 := by
  have hc : ((97397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).1
  have hw2 : ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4775277513/500000000000 : ℚ) : ℝ)
      = ((49029/1000000 : ℚ) : ℝ) * ((97397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c417 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((158807/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2206233/10000000) (δ := 2579/250000000) (ψ := -122331/1000000) 205 197
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t417 : ((77761984239/2500000000000 : ℚ) : ℝ) ≤ stT205 417 := by
  have hc : ((317589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).1
  have hw2 : ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((244851/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77761984239/2500000000000 : ℚ) : ℝ)
      = ((244851/5000000 : ℚ) : ℝ) * ((317589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c418 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((462173/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -978693/10000000) (δ := 2579/250000000) (ψ := -122331/1000000) 205 197
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t418 : ((11302175951/250000000000 : ℚ) : ℝ) ≤ stT205 418 := by
  have hc : ((115537/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).1
  have hw2 : ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((97823/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11302175951/250000000000 : ℚ) : ℝ)
      = ((97823/2000000 : ℚ) : ℝ) * ((115537/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c419 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((497583/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 122963/5000000) (δ := 651/62500000) (ψ := -122331/1000000) 205 197
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t419 : ((121536253649/2500000000000 : ℚ) : ℝ) ≤ stT205 419 := by
  have hc : ((248779/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121536253649/2500000000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((248779/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c420 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((832579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1467623/10000000) (δ := 10287/1000000000) (ψ := -122331/1000000) 205 197
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t420 : ((8124650511/200000000000 : ℚ) : ℝ) ≤ stT205 420 := by
  have hc : ((832529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8124650511/200000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((832529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c421 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((11903/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2686399/10000000) (δ := 10387/1000000000) (ψ := -122331/1000000) 205 197
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t421 : ((2320222359/100000000000 : ℚ) : ℝ) ≤ stT205 421 := by
  have hc : ((47607/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2320222359/100000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((47607/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c422 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((4937/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1951153/5000000) (δ := 651/62500000) (ψ := -122331/1000000) 205 197
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t422 : ((18680643/39062500000 : ℚ) : ℝ) ≤ stT205 422 := by
  have hc : ((307/31250 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18680643/39062500000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((307/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c423 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-457623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5115291/10000000) (δ := 651/62500000) (ψ := -122331/1000000) 205 197
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t423 : ((-222528393041/10000000000000 : ℚ) : ℝ) ≤ stT205 423 := by
  have hc : ((-457673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).2
  have h0 : (0:ℝ) ≤ ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222528393041/10000000000000 : ℚ) : ℝ)
      = ((486217/10000000 : ℚ) : ℝ) * ((-457673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c424 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-20471/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6325457/10000000) (δ := 2579/250000000) (ψ := -122331/1000000) 205 197
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t424 : ((-39768819627/1000000000000 : ℚ) : ℝ) ≤ stT205 424 := by
  have hc : ((-81889/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).2
  have h0 : (0:ℝ) ≤ ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39768819627/1000000000000 : ℚ) : ℝ)
      = ((485643/10000000 : ℚ) : ℝ) * ((-81889/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c425 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-247939/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7532753/10000000) (δ := 10287/1000000000) (ψ := -122331/1000000) 205 197
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t425 : ((-15034291251/312500000000 : ℚ) : ℝ) ≤ stT205 425 := by
  have hc : ((-495903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15034291251/312500000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-495903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c426 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-234559/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6970733/10000000) (δ := 519/50000000) (ψ := -122331/1000000) 205 198
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t426 : ((-113650360893/2500000000000 : ℚ) : ℝ) ≤ stT205 426 := by
  have hc : ((-469143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113650360893/2500000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-469143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c427 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-335973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2884537/5000000) (δ := 257/25000000) (ψ := -122331/1000000) 205 198
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t427 : ((-40650214033/1250000000000 : ℚ) : ℝ) ≤ stT205 427 := by
  have hc : ((-167999/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40650214033/1250000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-167999/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c428 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-254487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -914057/2000000) (δ := 10323/1000000000) (ψ := -122331/1000000) 205 198
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t428 : ((-123035295153/10000000000000 : ℚ) : ℝ) ≤ stT205 428 := by
  have hc : ((-254537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123035295153/10000000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-254537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c429 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((109657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3374213/10000000) (δ := 519/50000000) (ψ := -122331/1000000) 205 198
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t429 : ((206760813/19531250000 : ℚ) : ℝ) ≤ stT205 429 := by
  have hc : ((3426/15625 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).1
  have hw2 : ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((120701/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((206760813/19531250000 : ℚ) : ℝ)
      = ((120701/2500000 : ℚ) : ℝ) * ((3426/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c430 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((643003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2180959/10000000) (δ := 257/25000000) (ψ := -122331/1000000) 205 198
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t430 : ((155029470313/5000000000000 : ℚ) : ℝ) ≤ stT205 430 := by
  have hc : ((642953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).1
  have hw2 : ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((241121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155029470313/5000000000000 : ℚ) : ℝ)
      = ((241121/5000000 : ℚ) : ℝ) * ((642953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c431 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((92253/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -247631/2500000) (δ := 257/25000000) (ψ := -122331/1000000) 205 198
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t431 : ((5554286673/125000000000 : ℚ) : ℝ) ≤ stT205 431 := by
  have hc : ((11531/12500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5554286673/125000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((11531/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c432 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((996891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39439/2000000) (δ := 10323/1000000000) (ψ := -122331/1000000) 205 198
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t432 : ((3836841009/80000000000 : ℚ) : ℝ) ≤ stT205 432 := by
  have hc : ((996841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3836841009/80000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((996841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c433 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((106377/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1382197/10000000) (δ := 519/50000000) (ψ := -122331/1000000) 205 198
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t433 : ((204473939827/5000000000000 : ℚ) : ℝ) ≤ stT205 433 := by
  have hc : ((425483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204473939827/5000000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((425483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c434 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((259219/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 160277/625000) (δ := 519/50000000) (ψ := -122331/1000000) 205 198
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t434 : ((12441700791/500000000000 : ℚ) : ℝ) ≤ stT205 434 := by
  have hc : ((129597/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12441700791/500000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((129597/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c435 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((73151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3743951/10000000) (δ := 257/25000000) (ψ := -122331/1000000) 205 198
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t435 : ((35049224763/10000000000000 : ℚ) : ℝ) ≤ stT205 435 := by
  have hc : ((73101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35049224763/10000000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((73101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c436 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-387119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2460377/5000000) (δ := 10423/1000000000) (ψ := -122331/1000000) 205 198
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t436 : ((-92710327233/5000000000000 : ℚ) : ℝ) ≤ stT205 436 := by
  have hc : ((-387169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).2
  have h0 : (0:ℝ) ≤ ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92710327233/5000000000000 : ℚ) : ℝ)
      = ((239457/5000000 : ℚ) : ℝ) * ((-387169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c437 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-762481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 152371/250000) (δ := 10323/1000000000) (ψ := -122331/1000000) 205 198
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t437 : ((-72953628363/2000000000000 : ℚ) : ℝ) ≤ stT205 437 := by
  have hc : ((-762531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).2
  have h0 : (0:ℝ) ≤ ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72953628363/2000000000000 : ℚ) : ℝ)
      = ((95673/2000000 : ℚ) : ℝ) * ((-762531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c438 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-972499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 908289/1250000) (δ := 519/50000000) (ψ := -122331/1000000) 205 198
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t438 : ((-464702390631/10000000000000 : ℚ) : ℝ) ≤ stT205 438 := by
  have hc : ((-972549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-464702390631/10000000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-972549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c439 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-243277/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1454579/2000000) (δ := 10373/1000000000) (ψ := -122331/1000000) 205 199
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t439 : ((-116115752823/2500000000000 : ℚ) : ℝ) ≤ stT205 439 := by
  have hc : ((-486579/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116115752823/2500000000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-486579/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c440 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-765569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6106803/10000000) (δ := 1043/100000000) (ψ := -122331/1000000) 205 199
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t440 : ((-91248769277/2500000000000 : ℚ) : ℝ) ≤ stT205 440 := by
  have hc : ((-765619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91248769277/2500000000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-765619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c441 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-395447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4943377/10000000) (δ := 1033/100000000) (ψ := -122331/1000000) 205 199
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t441 : ((-188332111927/10000000000000 : ℚ) : ℝ) ≤ stT205 441 := by
  have hc : ((-395497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188332111927/10000000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-395497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c442 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((28869/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -756513/2000000) (δ := 10373/1000000000) (ψ := -122331/1000000) 205 199
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t442 : ((3429919361/1250000000000 : ℚ) : ℝ) ≤ stT205 442 := by
  have hc : ((7211/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).1
  have hw2 : ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((475651/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3429919361/1250000000000 : ℚ) : ℝ)
      = ((475651/10000000 : ℚ) : ℝ) * ((7211/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c443 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((497791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1312183/5000000) (δ := 10273/1000000000) (ψ := -122331/1000000) 205 199
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t443 : ((118241858737/5000000000000 : ℚ) : ℝ) ≤ stT205 443 := by
  have hc : ((497741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).1
  have hw2 : ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237557/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118241858737/5000000000000 : ℚ) : ℝ)
      = ((237557/5000000 : ℚ) : ℝ) * ((497741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c444 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((416161/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1468781/10000000) (δ := 10273/1000000000) (ψ := -122331/1000000) 205 199
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t444 : ((12343061913/312500000000 : ℚ) : ℝ) ≤ stT205 444 := by
  have hc : ((52017/62500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).1
  have hw2 : ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237289/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12343061913/312500000000 : ℚ) : ℝ)
      = ((237289/5000000 : ℚ) : ℝ) * ((52017/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c445 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((31001/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -31581/1000000) (δ := 10373/1000000000) (ψ := -122331/1000000) 205 199
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t445 : ((47024410719/1000000000000 : ℚ) : ℝ) ≤ stT205 445 := by
  have hc : ((495991/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).1
  have hw2 : ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94809/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47024410719/1000000000000 : ℚ) : ℝ)
      = ((94809/2000000 : ℚ) : ℝ) * ((495991/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c446 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((944791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 834599/10000000) (δ := 10273/1000000000) (ψ := -122331/1000000) 205 199
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t446 : ((447347145133/10000000000000 : ℚ) : ℝ) ≤ stT205 446 := by
  have hc : ((944741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((447347145133/10000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((944741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c447 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((701741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 991197/5000000) (δ := 10273/1000000000) (ψ := -122331/1000000) 205 199
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t447 : ((331887914253/10000000000000 : ℚ) : ℝ) ≤ stT205 447 := by
  have hc : ((701691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((331887914253/10000000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((701691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c448 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((157153/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1563839/5000000) (δ := 1033/100000000) (ψ := -122331/1000000) 205 199
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t448 : ((1855897731/125000000000 : ℚ) : ℝ) ≤ stT205 448 := by
  have hc : ((19641/62500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1855897731/125000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((19641/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c449 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-136911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1067587/2500000) (δ := 1033/100000000) (ψ := -122331/1000000) 205 199
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t449 : ((-6463600473/1000000000000 : ℚ) : ℝ) ≤ stT205 449 := by
  have hc : ((-136961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).2
  have h0 : (0:ℝ) ≤ ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6463600473/1000000000000 : ℚ) : ℝ)
      = ((47193/1000000 : ℚ) : ℝ) * ((-136961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c450 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-139797/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5410507/10000000) (δ := 1043/100000000) (ψ := -122331/1000000) 205 199
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t450 : ((-26362758939/1000000000000 : ℚ) : ℝ) ≤ stT205 450 := by
  have hc : ((-279619/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).2
  have h0 : (0:ℝ) ≤ ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26362758939/1000000000000 : ℚ) : ℝ)
      = ((94281/2000000 : ℚ) : ℝ) * ((-279619/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c451 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-866659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3274077/5000000) (δ := 10273/1000000000) (ψ := -122331/1000000) 205 199
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t451 : ((-204058833669/5000000000000 : ℚ) : ℝ) ≤ stT205 451 := by
  have hc : ((-866709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204058833669/5000000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-866709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c452 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-997669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7683239/10000000) (δ := 10273/1000000000) (ψ := -122331/1000000) 205 199
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t452 : ((-469288106559/10000000000000 : ℚ) : ℝ) ≤ stT205 452 := by
  have hc : ((-997719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-469288106559/10000000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-997719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c453 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-926891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6892099/10000000) (δ := 10337/1000000000) (ψ := -122331/1000000) 205 200
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t453 : ((-435514886381/10000000000000 : ℚ) : ℝ) ≤ stT205 453 := by
  have hc : ((-926941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-435514886381/10000000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-926941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c454 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-669859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5762037/10000000) (δ := 5183/500000000) (ψ := -122331/1000000) 205 200
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t454 : ((-78601092879/2500000000000 : ℚ) : ℝ) ≤ stT205 454 := by
  have hc : ((-669909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78601092879/2500000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-669909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c455 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-69799/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4634383/10000000) (δ := 5133/500000000) (ψ := -122331/1000000) 205 200
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t455 : ((-8182047423/625000000000 : ℚ) : ℝ) ≤ stT205 455 := by
  have hc : ((-139623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8182047423/625000000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-139623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c456 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((41581/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87731/250000) (δ := 10437/1000000000) (ψ := -122331/1000000) 205 200
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t456 : ((9733098001/1250000000000 : ℚ) : ℝ) ≤ stT205 456 := by
  have hc : ((83137/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).1
  have hw2 : ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117073/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9733098001/1250000000000 : ℚ) : ℝ)
      = ((117073/2500000 : ℚ) : ℝ) * ((83137/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c457 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((5779/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2386609/10000000) (δ := 10337/1000000000) (ψ := -122331/1000000) 205 200
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t457 : ((270306673/10000000000 : ℚ) : ℝ) ≤ stT205 457 := by
  have hc : ((11557/20000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).1
  have hw2 : ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((23389/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270306673/10000000000 : ℚ) : ℝ)
      = ((23389/500000 : ℚ) : ℝ) * ((11557/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c458 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((874421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1266387/10000000) (δ := 5183/500000000) (ψ := -122331/1000000) 205 200
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t458 : ((408566462799/10000000000000 : ℚ) : ℝ) ≤ stT205 458 := by
  have hc : ((874371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).1
  have hw2 : ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((467269/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((408566462799/10000000000000 : ℚ) : ℝ)
      = ((467269/10000000 : ℚ) : ℝ) * ((874371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c459 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((199647/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -148573/10000000) (δ := 5133/500000000) (ψ := -122331/1000000) 205 200
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t459 : ((2329564153/50000000000 : ℚ) : ℝ) ≤ stT205 459 := by
  have hc : ((199637/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).1
  have hw2 : ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11669/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2329564153/50000000000 : ℚ) : ℝ)
      = ((11669/250000 : ℚ) : ℝ) * ((199637/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c460 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((463081/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 96673/1000000) (δ := 10437/1000000000) (ψ := -122331/1000000) 205 200
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t460 : ((3373449783/78125000000 : ℚ) : ℝ) ≤ stT205 460 := by
  have hc : ((28941/31250 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3373449783/78125000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((28941/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c461 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((134699/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 83187/400000) (δ := 10437/1000000000) (ψ := -122331/1000000) 205 200
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t461 : ((31365431497/1000000000000 : ℚ) : ℝ) ≤ stT205 461 := by
  have hc : ((134689/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31365431497/1000000000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((134689/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c462 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((72621/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39877/125000) (δ := 10437/1000000000) (ψ := -122331/1000000) 205 200
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t462 : ((33780523757/2500000000000 : ℚ) : ℝ) ≤ stT205 462 := by
  have hc : ((145217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33780523757/2500000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((145217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c463 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-147973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4298287/10000000) (δ := 5133/500000000) (ψ := -122331/1000000) 205 200
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t463 : ((-3439610451/500000000000 : ℚ) : ℝ) ≤ stT205 463 := by
  have hc : ((-148023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).2
  have h0 : (0:ℝ) ≤ ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3439610451/500000000000 : ℚ) : ℝ)
      = ((23237/500000 : ℚ) : ℝ) * ((-148023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c464 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-557031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2702003/5000000) (δ := 10337/1000000000) (ψ := -122331/1000000) 205 200
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t464 : ((-258618726359/10000000000000 : ℚ) : ℝ) ≤ stT205 464 := by
  have hc : ((-557081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).2
  have h0 : (0:ℝ) ≤ ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258618726359/10000000000000 : ℚ) : ℝ)
      = ((464239/10000000 : ℚ) : ℝ) * ((-557081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c465 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-214601/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6507367/10000000) (δ := 5133/500000000) (ψ := -122331/1000000) 205 200
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t465 : ((-199049299753/5000000000000 : ℚ) : ℝ) ≤ stT205 465 := by
  have hc : ((-429227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).2
  have h0 : (0:ℝ) ≤ ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199049299753/5000000000000 : ℚ) : ℝ)
      = ((463739/10000000 : ℚ) : ℝ) * ((-429227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c466 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-124397/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11888/15625) (δ := 10437/1000000000) (ψ := -122331/1000000) 205 200
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t466 : ((-115257620673/2500000000000 : ℚ) : ℝ) ≤ stT205 466 := by
  have hc : ((-497613/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).2
  have h0 : (0:ℝ) ≤ ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115257620673/2500000000000 : ℚ) : ℝ)
      = ((231621/5000000 : ℚ) : ℝ) * ((-497613/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c467 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-942363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7001049/10000000) (δ := 5179/500000000) (ψ := -122331/1000000) 205 201
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t467 : ((-87219380737/2000000000000 : ℚ) : ℝ) ≤ stT205 467 := by
  have hc : ((-942413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87219380737/2000000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-942413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c468 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-711147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5904811/10000000) (δ := 2069/200000000) (ψ := -122331/1000000) 205 201
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t468 : ((-328751524447/10000000000000 : ℚ) : ℝ) ≤ stT205 468 := by
  have hc : ((-711197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-328751524447/10000000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-711197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c469 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-86559/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7517/15625) (δ := 5129/500000000) (ψ := -122331/1000000) 205 201
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t469 : ((-39975082697/2500000000000 : ℚ) : ℝ) ≤ stT205 469 := by
  have hc : ((-173143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39975082697/2500000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-173143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c470 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((41489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1859653/5000000) (δ := 2069/200000000) (ψ := -122331/1000000) 205 201
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t470 : ((478147299/125000000000 : ℚ) : ℝ) ≤ stT205 470 := by
  have hc : ((5183/62500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).1
  have hw2 : ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((92253/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((478147299/125000000000 : ℚ) : ℝ)
      = ((92253/2000000 : ℚ) : ℝ) * ((5183/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c471 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((247911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2630039/10000000) (δ := 5179/500000000) (ψ := -122331/1000000) 205 201
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t471 : ((2284393433/100000000000 : ℚ) : ℝ) ≤ stT205 471 := by
  have hc : ((123943/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).1
  have hw2 : ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18431/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2284393433/100000000000 : ℚ) : ℝ)
      = ((18431/400000 : ℚ) : ℝ) * ((123943/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c472 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((203871/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1543077/10000000) (δ := 2089/200000000) (ψ := -122331/1000000) 205 201
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t472 : ((187666834779/5000000000000 : ℚ) : ℝ) ≤ stT205 472 := by
  have hc : ((407717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187666834779/5000000000000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((407717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c473 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((196647/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -229211/5000000) (δ := 2089/200000000) (ψ := -122331/1000000) 205 201
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t473 : ((452068463/10000000000 : ℚ) : ℝ) ≤ stT205 473 := by
  have hc : ((196637/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((452068463/10000000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((196637/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c474 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((969013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 311989/5000000) (δ := 2089/200000000) (ψ := -122331/1000000) 205 201
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t474 : ((89011848069/2000000000000 : ℚ) : ℝ) ≤ stT205 474 := by
  have hc : ((968963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89011848069/2000000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((968963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c475 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((194137/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1704071/10000000) (δ := 5179/500000000) (ψ := -122331/1000000) 205 201
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t475 : ((178140676919/5000000000000 : ℚ) : ℝ) ≤ stT205 475 := by
  have hc : ((388249/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178140676919/5000000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((388249/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c476 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((221101/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2781859/10000000) (δ := 2069/200000000) (ψ := -122331/1000000) 205 201
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t476 : ((25332490881/1250000000000 : ℚ) : ℝ) ≤ stT205 476 := by
  have hc : ((55269/125000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25332490881/1250000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((55269/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c477 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((6959/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3857391/10000000) (δ := 5179/500000000) (ψ := -122331/1000000) 205 201
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t477 : ((1590290031/1250000000000 : ℚ) : ℝ) ≤ stT205 477 := by
  have hc : ((13893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1590290031/1250000000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((13893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c478 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-48849/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30817/62500) (δ := 5129/500000000) (ψ := -122331/1000000) 205 201
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t478 : ((-8938361119/500000000000 : ℚ) : ℝ) ≤ stT205 478 := by
  have hc : ((-195421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8938361119/500000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-195421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c479 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-92233/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6001743/10000000) (δ := 2089/200000000) (ψ := -122331/1000000) 205 201
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t479 : ((-10536305049/312500000000 : ℚ) : ℝ) ≤ stT205 479 := by
  have hc : ((-368957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10536305049/312500000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-368957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c480 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-951307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7070613/10000000) (δ := 2089/200000000) (ψ := -122331/1000000) 205 201
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t480 : ((-108558395913/2500000000000 : ℚ) : ℝ) ≤ stT205 480 := by
  have hc : ((-951357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108558395913/2500000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-951357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c481 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-993591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7570787/10000000) (δ := 2563/250000000) (ψ := -122331/1000000) 205 202
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t481 : ((-453061544001/10000000000000 : ℚ) : ℝ) ≤ stT205 481 := by
  have hc : ((-993641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-453061544001/10000000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-993641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c482 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-858201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -813297/1250000) (δ := 10351/1000000000) (ψ := -122331/1000000) 205 202
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t482 : ((-6108172367/156250000000 : ℚ) : ℝ) ≤ stT205 482 := by
  have hc : ((-858251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).2
  have h0 : (0:ℝ) ≤ ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6108172367/156250000000 : ℚ) : ℝ)
      = ((7117/156250 : ℚ) : ℝ) * ((-858251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c483 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-570317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -272211/500000) (δ := 10451/1000000000) (ψ := -122331/1000000) 205 202
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t483 : ((-32440763859/1250000000000 : ℚ) : ℝ) ≤ stT205 483 := by
  have hc : ((-570367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).2
  have h0 : (0:ℝ) ≤ ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32440763859/1250000000000 : ℚ) : ℝ)
      = ((56877/1250000 : ℚ) : ℝ) * ((-570367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c484 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-11367/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -548027/1250000) (δ := 10351/1000000000) (ψ := -122331/1000000) 205 202
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t484 : ((-20672979353/2500000000000 : ℚ) : ℝ) ≤ stT205 484 := by
  have hc : ((-90961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).2
  have h0 : (0:ℝ) ≤ ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20672979353/2500000000000 : ℚ) : ℝ)
      = ((227273/5000000 : ℚ) : ℝ) * ((-90961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c485 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((118953/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3326467/10000000) (δ := 2563/250000000) (ψ := -122331/1000000) 205 202
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t485 : ((843786727/78125000000 : ℚ) : ℝ) ≤ stT205 485 := by
  have hc : ((7433/31250 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((843786727/78125000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((7433/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c486 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((123013/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -113541/500000) (δ := 10451/1000000000) (ψ := -122331/1000000) 205 202
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t486 : ((55795267827/2000000000000 : ℚ) : ℝ) ≤ stT205 486 := by
  have hc : ((123003/200000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55795267827/2000000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((123003/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c487 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((220941/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -38043/312500) (δ := 10351/1000000000) (ψ := -122331/1000000) 205 202
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t487 : ((200224406551/5000000000000 : ℚ) : ℝ) ≤ stT205 487 := by
  have hc : ((441857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).1
  have hw2 : ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453143/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200224406551/5000000000000 : ℚ) : ℝ)
      = ((453143/10000000 : ℚ) : ℝ) * ((441857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c488 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((498897/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33217/2000000) (δ := 10451/1000000000) (ψ := -122331/1000000) 205 202
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t488 : ((14114273701/312500000000 : ℚ) : ℝ) ≤ stT205 488 := by
  have hc : ((62359/62500 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).1
  have hw2 : ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((226339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14114273701/312500000000 : ℚ) : ℝ)
      = ((226339/5000000 : ℚ) : ℝ) * ((62359/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c489 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((93827/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 883003/10000000) (δ := 2563/250000000) (ψ := -122331/1000000) 205 202
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t489 : ((4242771573/100000000000 : ℚ) : ℝ) ≤ stT205 489 := by
  have hc : ((46911/50000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).1
  have hw2 : ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90443/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4242771573/100000000000 : ℚ) : ℝ)
      = ((90443/2000000 : ℚ) : ℝ) * ((46911/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c490 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((17913/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1929989/10000000) (δ := 10351/1000000000) (ψ := -122331/1000000) 205 202
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t490 : ((32366747191/1000000000000 : ℚ) : ℝ) ≤ stT205 490 := by
  have hc : ((71647/100000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).1
  have hw2 : ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451753/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32366747191/1000000000000 : ℚ) : ℝ)
      = ((451753/10000000 : ℚ) : ℝ) * ((71647/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c491 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((371707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1487437/5000000) (δ := 10351/1000000000) (ψ := -122331/1000000) 205 202
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t491 : ((167726202501/10000000000000 : ℚ) : ℝ) ≤ stT205 491 := by
  have hc : ((371657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).1
  have hw2 : ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451293/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167726202501/10000000000000 : ℚ) : ℝ)
      = ((451293/10000000 : ℚ) : ℝ) * ((371657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c492 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-36239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4017607/10000000) (δ := 647/62500000) (ψ := -122331/1000000) 205 202
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t492 : ((-3272070263/2000000000000 : ℚ) : ℝ) ≤ stT205 492 := by
  have hc : ((-36289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).2
  have h0 : (0:ℝ) ≤ ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3272070263/2000000000000 : ℚ) : ℝ)
      = ((90167/2000000 : ℚ) : ℝ) * ((-36289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c493 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-109299/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5058187/10000000) (δ := 647/62500000) (ψ := -122331/1000000) 205 202
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t493 : ((-49231494747/2500000000000 : ℚ) : ℝ) ≤ stT205 493 := by
  have hc : ((-218623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).2
  have h0 : (0:ℝ) ≤ ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49231494747/2500000000000 : ℚ) : ℝ)
      = ((225189/5000000 : ℚ) : ℝ) * ((-218623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c494 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-762967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6096717/10000000) (δ := 647/62500000) (ψ := -122331/1000000) 205 202
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t494 : ((-171649067337/5000000000000 : ℚ) : ℝ) ≤ stT205 494 := by
  have hc : ((-763017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).2
  have h0 : (0:ℝ) ≤ ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171649067337/5000000000000 : ℚ) : ℝ)
      = ((224961/5000000 : ℚ) : ℝ) * ((-763017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c495 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-958713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3566547/5000000) (δ := 10351/1000000000) (ψ := -122331/1000000) 205 202
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t495 : ((-430932329321/10000000000000 : ℚ) : ℝ) ≤ stT205 495 := by
  have hc : ((-958763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).2
  have h0 : (0:ℝ) ≤ ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-430932329321/10000000000000 : ℚ) : ℝ)
      = ((449467/10000000 : ℚ) : ℝ) * ((-958763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c496 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-992151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3770271/5000000) (δ := 2611/250000000) (ψ := -122331/1000000) 205 203
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t496 : ((-222756069907/5000000000000 : ℚ) : ℝ) ≤ stT205 496 := by
  have hc : ((-992201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).2
  have h0 : (0:ℝ) ≤ ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222756069907/5000000000000 : ℚ) : ℝ)
      = ((224507/5000000 : ℚ) : ℝ) * ((-992201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c497 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-858599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1301663/2000000) (δ := 10359/1000000000) (ψ := -122331/1000000) 205 203
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t497 : ((-192578656369/5000000000000 : ℚ) : ℝ) ≤ stT205 497 := by
  have hc : ((-858649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192578656369/5000000000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-858649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c498 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-23257/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -547819/1000000) (δ := 10359/1000000000) (ψ := -122331/1000000) 205 203
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t498 : ((-10422613749/400000000000 : ℚ) : ℝ) ≤ stT205 498 := by
  have hc : ((-23259/40000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10422613749/400000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-23259/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c499 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-103863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -890023/2000000) (δ := 10359/1000000000) (ψ := -122331/1000000) 205 203
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t499 : ((-1453334683/156250000000 : ℚ) : ℝ) ≤ stT205 499 := by
  have hc : ((-6493/31250 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1453334683/156250000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-6493/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_c500 :
    |Real.cos (((205 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((99903/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -342409/1000000) (δ := 10359/1000000000) (ψ := -122331/1000000) 205 203
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st205_t500 : ((22333370007/2500000000000 : ℚ) : ℝ) ≤ stT205 500 := by
  have hc : ((49939/250000 : ℚ) : ℝ)
      ≤ Real.cos (((205 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st205_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).1
  have hw2 : ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22333370007/2500000000000 : ℚ) : ℝ)
      = ((447213/10000000 : ℚ) : ℝ) * ((49939/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st205_p1 : ((992477/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT205 (i+1) := by
  rw [Finset.sum_range_one]
  exact st205_t1

theorem st205_p2 : ((654438300373/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT205 (i+1))
      = (∑ i ∈ Finset.range 1, stT205 (i+1)) + stT205 2 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 1
    simpa using h
  have hprev := st205_p1
  have hstep := st205_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p3 : ((4507960228529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT205 (i+1))
      = (∑ i ∈ Finset.range 2, stT205 (i+1)) + stT205 3 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 2
    simpa using h
  have hprev := st205_p2
  have hstep := st205_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p4 : ((4511490228529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT205 (i+1))
      = (∑ i ∈ Finset.range 3, stT205 (i+1)) + stT205 4 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 3
    simpa using h
  have hprev := st205_p3
  have hstep := st205_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p5 : ((2315501511361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT205 (i+1))
      = (∑ i ∈ Finset.range 4, stT205 (i+1)) + stT205 5 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 4
    simpa using h
  have hprev := st205_p4
  have hstep := st205_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p6 : ((292271926357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT205 (i+1))
      = (∑ i ∈ Finset.range 5, stT205 (i+1)) + stT205 6 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 5
    simpa using h
  have hprev := st205_p5
  have hstep := st205_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p7 : ((-3190251862751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT205 (i+1))
      = (∑ i ∈ Finset.range 6, stT205 (i+1)) + stT205 7 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 6
    simpa using h
  have hprev := st205_p6
  have hstep := st205_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p8 : ((-853724169041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT205 (i+1))
      = (∑ i ∈ Finset.range 7, stT205 (i+1)) + stT205 8 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 7
    simpa using h
  have hprev := st205_p7
  have hstep := st205_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p9 : ((-1727507677131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT205 (i+1))
      = (∑ i ∈ Finset.range 8, stT205 (i+1)) + stT205 9 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 8
    simpa using h
  have hprev := st205_p8
  have hstep := st205_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p10 : ((20474792501/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT205 (i+1))
      = (∑ i ∈ Finset.range 9, stT205 (i+1)) + stT205 10 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 9
    simpa using h
  have hprev := st205_p9
  have hstep := st205_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p11 : ((54656768341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT205 (i+1))
      = (∑ i ∈ Finset.range 10, stT205 (i+1)) + stT205 11 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 10
    simpa using h
  have hprev := st205_p10
  have hstep := st205_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p12 : ((250759162647/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT205 (i+1))
      = (∑ i ∈ Finset.range 11, stT205 (i+1)) + stT205 12 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 11
    simpa using h
  have hprev := st205_p11
  have hstep := st205_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p13 : ((435364087809/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT205 (i+1))
      = (∑ i ∈ Finset.range 12, stT205 (i+1)) + stT205 13 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 12
    simpa using h
  have hprev := st205_p12
  have hstep := st205_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p14 : ((456301195177/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT205 (i+1))
      = (∑ i ∈ Finset.range 13, stT205 (i+1)) + stT205 14 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 13
    simpa using h
  have hprev := st205_p13
  have hstep := st205_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p15 : ((1831617779981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT205 (i+1))
      = (∑ i ∈ Finset.range 14, stT205 (i+1)) + stT205 15 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 14
    simpa using h
  have hprev := st205_p14
  have hstep := st205_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p16 : ((-162231428059/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT205 (i+1))
      = (∑ i ∈ Finset.range 15, stT205 (i+1)) + stT205 16 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 15
    simpa using h
  have hprev := st205_p15
  have hstep := st205_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p17 : ((-2990644276091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT205 (i+1))
      = (∑ i ∈ Finset.range 16, stT205 (i+1)) + stT205 17 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 16
    simpa using h
  have hprev := st205_p16
  have hstep := st205_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p18 : ((-4033617525499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT205 (i+1))
      = (∑ i ∈ Finset.range 17, stT205 (i+1)) + stT205 18 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 17
    simpa using h
  have hprev := st205_p17
  have hstep := st205_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p19 : ((-1036876806377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT205 (i+1))
      = (∑ i ∈ Finset.range 18, stT205 (i+1)) + stT205 19 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 18
    simpa using h
  have hprev := st205_p18
  have hstep := st205_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p20 : ((-963108956047/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT205 (i+1))
      = (∑ i ∈ Finset.range 19, stT205 (i+1)) + stT205 20 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 19
    simpa using h
  have hprev := st205_p19
  have hstep := st205_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p21 : ((-808816953743/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT205 (i+1))
      = (∑ i ∈ Finset.range 20, stT205 (i+1)) + stT205 21 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 20
    simpa using h
  have hprev := st205_p20
  have hstep := st205_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p22 : ((-70966345829/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT205 (i+1))
      = (∑ i ∈ Finset.range 21, stT205 (i+1)) + stT205 22 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 21
    simpa using h
  have hprev := st205_p21
  have hstep := st205_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p23 : ((-266797898657/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT205 (i+1))
      = (∑ i ∈ Finset.range 22, stT205 (i+1)) + stT205 23 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 22
    simpa using h
  have hprev := st205_p22
  have hstep := st205_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p24 : ((-1593566073457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT205 (i+1))
      = (∑ i ∈ Finset.range 23, stT205 (i+1)) + stT205 24 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 23
    simpa using h
  have hprev := st205_p23
  have hstep := st205_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p25 : ((-626567073457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT205 (i+1))
      = (∑ i ∈ Finset.range 24, stT205 (i+1)) + stT205 25 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 24
    simpa using h
  have hprev := st205_p24
  have hstep := st205_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p26 : ((-1047550108377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT205 (i+1))
      = (∑ i ∈ Finset.range 25, stT205 (i+1)) + stT205 26 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 25
    simpa using h
  have hprev := st205_p25
  have hstep := st205_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p27 : ((-1959024573993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT205 (i+1))
      = (∑ i ∈ Finset.range 26, stT205 (i+1)) + stT205 27 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 26
    simpa using h
  have hprev := st205_p26
  have hstep := st205_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p28 : ((-1013588630421/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT205 (i+1))
      = (∑ i ∈ Finset.range 27, stT205 (i+1)) + stT205 28 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 27
    simpa using h
  have hprev := st205_p27
  have hstep := st205_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p29 : ((-2673674684077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT205 (i+1))
      = (∑ i ∈ Finset.range 28, stT205 (i+1)) + stT205 29 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 28
    simpa using h
  have hprev := st205_p28
  have hstep := st205_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p30 : ((-85197404891/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT205 (i+1))
      = (∑ i ∈ Finset.range 29, stT205 (i+1)) + stT205 30 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 29
    simpa using h
  have hprev := st205_p29
  have hstep := st205_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p31 : ((205128524199/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT205 (i+1))
      = (∑ i ∈ Finset.range 30, stT205 (i+1)) + stT205 31 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 30
    simpa using h
  have hprev := st205_p30
  have hstep := st205_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p32 : ((285144879819/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT205 (i+1))
      = (∑ i ∈ Finset.range 31, stT205 (i+1)) + stT205 32 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 31
    simpa using h
  have hprev := st205_p31
  have hstep := st205_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p33 : ((461819282417/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT205 (i+1))
      = (∑ i ∈ Finset.range 32, stT205 (i+1)) + stT205 33 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 32
    simpa using h
  have hprev := st205_p32
  have hstep := st205_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p34 : ((653904462357/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT205 (i+1))
      = (∑ i ∈ Finset.range 33, stT205 (i+1)) + stT205 34 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 33
    simpa using h
  have hprev := st205_p33
  have hstep := st205_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p35 : ((863683517313/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT205 (i+1))
      = (∑ i ∈ Finset.range 34, stT205 (i+1)) + stT205 35 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 34
    simpa using h
  have hprev := st205_p34
  have hstep := st205_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p36 : ((528222136771/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT205 (i+1))
      = (∑ i ∈ Finset.range 35, stT205 (i+1)) + stT205 36 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 35
    simpa using h
  have hprev := st205_p35
  have hstep := st205_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p37 : ((2315455939697/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT205 (i+1))
      = (∑ i ∈ Finset.range 36, stT205 (i+1)) + stT205 37 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 36
    simpa using h
  have hprev := st205_p36
  have hstep := st205_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p38 : ((548822590893/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT205 (i+1))
      = (∑ i ∈ Finset.range 37, stT205 (i+1)) + stT205 38 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 37
    simpa using h
  have hprev := st205_p37
  have hstep := st205_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p39 : ((3628510607319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT205 (i+1))
      = (∑ i ∈ Finset.range 38, stT205 (i+1)) + stT205 39 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 38
    simpa using h
  have hprev := st205_p38
  have hstep := st205_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p40 : ((6134237018209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT205 (i+1))
      = (∑ i ∈ Finset.range 39, stT205 (i+1)) + stT205 40 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 39
    simpa using h
  have hprev := st205_p39
  have hstep := st205_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p41 : ((6787495987939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT205 (i+1))
      = (∑ i ∈ Finset.range 40, stT205 (i+1)) + stT205 41 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 40
    simpa using h
  have hprev := st205_p40
  have hstep := st205_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p42 : ((8298455504001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT205 (i+1))
      = (∑ i ∈ Finset.range 41, stT205 (i+1)) + stT205 42 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 41
    simpa using h
  have hprev := st205_p41
  have hstep := st205_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p43 : ((8157314999729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT205 (i+1))
      = (∑ i ∈ Finset.range 42, stT205 (i+1)) + stT205 43 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 42
    simpa using h
  have hprev := st205_p42
  have hstep := st205_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p44 : ((26000321099/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT205 (i+1))
      = (∑ i ∈ Finset.range 43, stT205 (i+1)) + stT205 44 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 43
    simpa using h
  have hprev := st205_p43
  have hstep := st205_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p45 : ((6948719205621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT205 (i+1))
      = (∑ i ∈ Finset.range 44, stT205 (i+1)) + stT205 45 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 44
    simpa using h
  have hprev := st205_p44
  have hstep := st205_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p46 : ((1660832287767/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT205 (i+1))
      = (∑ i ∈ Finset.range 45, stT205 (i+1)) + stT205 46 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 45
    simpa using h
  have hprev := st205_p45
  have hstep := st205_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p47 : ((1471111516867/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT205 (i+1))
      = (∑ i ∈ Finset.range 46, stT205 (i+1)) + stT205 47 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 46
    simpa using h
  have hprev := st205_p46
  have hstep := st205_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p48 : ((1341287062547/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT205 (i+1))
      = (∑ i ∈ Finset.range 47, stT205 (i+1)) + stT205 48 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 47
    simpa using h
  have hprev := st205_p47
  have hstep := st205_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p49 : ((4067338156417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT205 (i+1))
      = (∑ i ∈ Finset.range 48, stT205 (i+1)) + stT205 49 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 48
    simpa using h
  have hprev := st205_p48
  have hstep := st205_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p50 : ((3673974532317/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT205 (i+1))
      = (∑ i ∈ Finset.range 49, stT205 (i+1)) + stT205 50 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 49
    simpa using h
  have hprev := st205_p49
  have hstep := st205_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p51 : ((1724170126691/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT205 (i+1))
      = (∑ i ∈ Finset.range 50, stT205 (i+1)) + stT205 51 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 50
    simpa using h
  have hprev := st205_p50
  have hstep := st205_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p52 : ((4085968596757/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT205 (i+1))
      = (∑ i ∈ Finset.range 51, stT205 (i+1)) + stT205 52 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 51
    simpa using h
  have hprev := st205_p51
  have hstep := st205_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p53 : ((3443081154183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT205 (i+1))
      = (∑ i ∈ Finset.range 52, stT205 (i+1)) + stT205 53 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 52
    simpa using h
  have hprev := st205_p52
  have hstep := st205_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p54 : ((1890809084727/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT205 (i+1))
      = (∑ i ∈ Finset.range 53, stT205 (i+1)) + stT205 54 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 53
    simpa using h
  have hprev := st205_p53
  have hstep := st205_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p55 : ((1924160385593/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT205 (i+1))
      = (∑ i ∈ Finset.range 54, stT205 (i+1)) + stT205 55 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 54
    simpa using h
  have hprev := st205_p54
  have hstep := st205_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p56 : ((6886426581509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT205 (i+1))
      = (∑ i ∈ Finset.range 55, stT205 (i+1)) + stT205 56 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 55
    simpa using h
  have hprev := st205_p55
  have hstep := st205_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p57 : ((8088861897217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT205 (i+1))
      = (∑ i ∈ Finset.range 56, stT205 (i+1)) + stT205 57 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 56
    simpa using h
  have hprev := st205_p56
  have hstep := st205_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p58 : ((6775783766567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT205 (i+1))
      = (∑ i ∈ Finset.range 57, stT205 (i+1)) + stT205 58 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 57
    simpa using h
  have hprev := st205_p57
  have hstep := st205_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p59 : ((3998471965783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT205 (i+1))
      = (∑ i ∈ Finset.range 58, stT205 (i+1)) + stT205 59 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 58
    simpa using h
  have hprev := st205_p58
  have hstep := st205_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p60 : ((6975205303741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT205 (i+1))
      = (∑ i ∈ Finset.range 59, stT205 (i+1)) + stT205 60 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 59
    simpa using h
  have hprev := st205_p59
  have hstep := st205_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p61 : ((7766369017933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT205 (i+1))
      = (∑ i ∈ Finset.range 60, stT205 (i+1)) + stT205 61 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 60
    simpa using h
  have hprev := st205_p60
  have hstep := st205_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p62 : ((7186221944317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT205 (i+1))
      = (∑ i ∈ Finset.range 61, stT205 (i+1)) + stT205 62 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 61
    simpa using h
  have hprev := st205_p61
  have hstep := st205_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p63 : ((3800694635183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT205 (i+1))
      = (∑ i ∈ Finset.range 62, stT205 (i+1)) + stT205 63 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 62
    simpa using h
  have hprev := st205_p62
  have hstep := st205_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p64 : ((7293222773833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT205 (i+1))
      = (∑ i ∈ Finset.range 63, stT205 (i+1)) + stT205 64 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 63
    simpa using h
  have hprev := st205_p63
  have hstep := st205_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p65 : ((7554489465913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT205 (i+1))
      = (∑ i ∈ Finset.range 64, stT205 (i+1)) + stT205 65 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 64
    simpa using h
  have hprev := st205_p64
  have hstep := st205_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p66 : ((3640479613679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT205 (i+1))
      = (∑ i ∈ Finset.range 65, stT205 (i+1)) + stT205 66 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 65
    simpa using h
  have hprev := st205_p65
  have hstep := st205_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p67 : ((3810937690723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT205 (i+1))
      = (∑ i ∈ Finset.range 66, stT205 (i+1)) + stT205 67 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 66
    simpa using h
  have hprev := st205_p66
  have hstep := st205_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p68 : ((3581867478339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT205 (i+1))
      = (∑ i ∈ Finset.range 67, stT205 (i+1)) + stT205 68 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 67
    simpa using h
  have hprev := st205_p67
  have hstep := st205_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p69 : ((388934424819/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT205 (i+1))
      = (∑ i ∈ Finset.range 68, stT205 (i+1)) + stT205 69 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 68
    simpa using h
  have hprev := st205_p68
  have hstep := st205_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p70 : ((3491628212753/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT205 (i+1))
      = (∑ i ∈ Finset.range 69, stT205 (i+1)) + stT205 70 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 69
    simpa using h
  have hprev := st205_p69
  have hstep := st205_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p71 : ((7956657762049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT205 (i+1))
      = (∑ i ∈ Finset.range 70, stT205 (i+1)) + stT205 71 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 70
    simpa using h
  have hprev := st205_p70
  have hstep := st205_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p72 : ((6843422363217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT205 (i+1))
      = (∑ i ∈ Finset.range 71, stT205 (i+1)) + stT205 72 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 71
    simpa using h
  have hprev := st205_p71
  have hstep := st205_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p73 : ((1602705343107/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT205 (i+1))
      = (∑ i ∈ Finset.range 72, stT205 (i+1)) + stT205 73 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 72
    simpa using h
  have hprev := st205_p72
  have hstep := st205_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p74 : ((691442214919/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT205 (i+1))
      = (∑ i ∈ Finset.range 73, stT205 (i+1)) + stT205 74 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 73
    simpa using h
  have hprev := st205_p73
  have hstep := st205_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p75 : ((778115844439/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT205 (i+1))
      = (∑ i ∈ Finset.range 74, stT205 (i+1)) + stT205 75 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 74
    simpa using h
  have hprev := st205_p74
  have hstep := st205_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p76 : ((228452995987/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT205 (i+1))
      = (∑ i ∈ Finset.range 75, stT205 (i+1)) + stT205 76 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 75
    simpa using h
  have hprev := st205_p75
  have hstep := st205_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p77 : ((726592702053/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT205 (i+1))
      = (∑ i ∈ Finset.range 76, stT205 (i+1)) + stT205 77 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 76
    simpa using h
  have hprev := st205_p76
  have hstep := st205_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p78 : ((7843604555437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT205 (i+1))
      = (∑ i ∈ Finset.range 77, stT205 (i+1)) + stT205 78 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 77
    simpa using h
  have hprev := st205_p77
  have hstep := st205_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p79 : ((6859027670669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT205 (i+1))
      = (∑ i ∈ Finset.range 78, stT205 (i+1)) + stT205 79 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 78
    simpa using h
  have hprev := st205_p78
  have hstep := st205_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p80 : ((7975144362107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT205 (i+1))
      = (∑ i ∈ Finset.range 79, stT205 (i+1)) + stT205 80 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 79
    simpa using h
  have hprev := st205_p79
  have hstep := st205_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p81 : ((1418471842287/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT205 (i+1))
      = (∑ i ∈ Finset.range 80, stT205 (i+1)) + stT205 81 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 80
    simpa using h
  have hprev := st205_p80
  have hstep := st205_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p82 : ((1482016777743/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT205 (i+1))
      = (∑ i ∈ Finset.range 81, stT205 (i+1)) + stT205 82 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 81
    simpa using h
  have hprev := st205_p81
  have hstep := st205_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p83 : ((7801643524091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT205 (i+1))
      = (∑ i ∈ Finset.range 82, stT205 (i+1)) + stT205 83 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 82
    simpa using h
  have hprev := st205_p82
  have hstep := st205_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p84 : ((6854448655471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT205 (i+1))
      = (∑ i ∈ Finset.range 83, stT205 (i+1)) + stT205 84 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 83
    simpa using h
  have hprev := st205_p83
  have hstep := st205_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p85 : ((1583654416623/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT205 (i+1))
      = (∑ i ∈ Finset.range 84, stT205 (i+1)) + stT205 85 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 84
    simpa using h
  have hprev := st205_p84
  have hstep := st205_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p86 : ((7282185805819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT205 (i+1))
      = (∑ i ∈ Finset.range 85, stT205 (i+1)) + stT205 86 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 85
    simpa using h
  have hprev := st205_p85
  have hstep := st205_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p87 : ((356586112553/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT205 (i+1))
      = (∑ i ∈ Finset.range 86, stT205 (i+1)) + stT205 87 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 86
    simpa using h
  have hprev := st205_p86
  have hstep := st205_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p88 : ((7992192410639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT205 (i+1))
      = (∑ i ∈ Finset.range 87, stT205 (i+1)) + stT205 88 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 87
    simpa using h
  have hprev := st205_p87
  have hstep := st205_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p89 : ((6951998353273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT205 (i+1))
      = (∑ i ∈ Finset.range 88, stT205 (i+1)) + stT205 89 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 88
    simpa using h
  have hprev := st205_p88
  have hstep := st205_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p90 : ((7481059777177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT205 (i+1))
      = (∑ i ∈ Finset.range 89, stT205 (i+1)) + stT205 90 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 89
    simpa using h
  have hprev := st205_p89
  have hstep := st205_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p91 : ((7840961881477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT205 (i+1))
      = (∑ i ∈ Finset.range 90, stT205 (i+1)) + stT205 91 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 90
    simpa using h
  have hprev := st205_p90
  have hstep := st205_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p92 : ((6850984604181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT205 (i+1))
      = (∑ i ∈ Finset.range 91, stT205 (i+1)) + stT205 92 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 91
    simpa using h
  have hprev := st205_p91
  have hstep := st205_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p93 : ((962889330337/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT205 (i+1))
      = (∑ i ∈ Finset.range 92, stT205 (i+1)) + stT205 93 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 92
    simpa using h
  have hprev := st205_p92
  have hstep := st205_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p94 : ((1921760756273/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT205 (i+1))
      = (∑ i ∈ Finset.range 93, stT205 (i+1)) + stT205 94 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 93
    simpa using h
  have hprev := st205_p93
  have hstep := st205_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p95 : ((6848447803673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT205 (i+1))
      = (∑ i ∈ Finset.range 94, stT205 (i+1)) + stT205 95 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 94
    simpa using h
  have hprev := st205_p94
  have hstep := st205_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p96 : ((7795865875413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT205 (i+1))
      = (∑ i ∈ Finset.range 95, stT205 (i+1)) + stT205 96 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 95
    simpa using h
  have hprev := st205_p95
  have hstep := st205_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p97 : ((7621366309299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT205 (i+1))
      = (∑ i ∈ Finset.range 96, stT205 (i+1)) + stT205 97 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 96
    simpa using h
  have hprev := st205_p96
  have hstep := st205_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p98 : ((1712903642751/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT205 (i+1))
      = (∑ i ∈ Finset.range 97, stT205 (i+1)) + stT205 98 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 97
    simpa using h
  have hprev := st205_p97
  have hstep := st205_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p99 : ((7793620675549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT205 (i+1))
      = (∑ i ∈ Finset.range 98, stT205 (i+1)) + stT205 99 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 98
    simpa using h
  have hprev := st205_p98
  have hstep := st205_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p100 : ((7660348675549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT205 (i+1))
      = (∑ i ∈ Finset.range 99, stT205 (i+1)) + stT205 100 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 99
    simpa using h
  have hprev := st205_p99
  have hstep := st205_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p101 : ((6840552787957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT205 (i+1))
      = (∑ i ∈ Finset.range 100, stT205 (i+1)) + stT205 101 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 100
    simpa using h
  have hprev := st205_p100
  have hstep := st205_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p102 : ((7700156827183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT205 (i+1))
      = (∑ i ∈ Finset.range 101, stT205 (i+1)) + stT205 102 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 101
    simpa using h
  have hprev := st205_p101
  have hstep := st205_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p103 : ((7788678784543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT205 (i+1))
      = (∑ i ∈ Finset.range 102, stT205 (i+1)) + stT205 103 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 102
    simpa using h
  have hprev := st205_p102
  have hstep := st205_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p104 : ((171444767197/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT205 (i+1))
      = (∑ i ∈ Finset.range 103, stT205 (i+1)) + stT205 104 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 103
    simpa using h
  have hprev := st205_p103
  have hstep := st205_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p105 : ((374724124319/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT205 (i+1))
      = (∑ i ∈ Finset.range 104, stT205 (i+1)) + stT205 105 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 104
    simpa using h
  have hprev := st205_p104
  have hstep := st205_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p106 : ((1589902210893/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT205 (i+1))
      = (∑ i ∈ Finset.range 105, stT205 (i+1)) + stT205 106 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 105
    simpa using h
  have hprev := st205_p105
  have hstep := st205_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p107 : ((1398265935383/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT205 (i+1))
      = (∑ i ∈ Finset.range 106, stT205 (i+1)) + stT205 107 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 106
    simpa using h
  have hprev := st205_p106
  have hstep := st205_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p108 : ((1436995920533/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT205 (i+1))
      = (∑ i ∈ Finset.range 107, stT205 (i+1)) + stT205 108 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 107
    simpa using h
  have hprev := st205_p107
  have hstep := st205_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p109 : ((8015537346393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT205 (i+1))
      = (∑ i ∈ Finset.range 108, stT205 (i+1)) + stT205 109 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 108
    simpa using h
  have hprev := st205_p108
  have hstep := st205_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p110 : ((7316645153541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT205 (i+1))
      = (∑ i ∈ Finset.range 109, stT205 (i+1)) + stT205 110 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 109
    simpa using h
  have hprev := st205_p109
  have hstep := st205_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p111 : ((6892069695297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT205 (i+1))
      = (∑ i ∈ Finset.range 110, stT205 (i+1)) + stT205 111 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 110
    simpa using h
  have hprev := st205_p110
  have hstep := st205_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p112 : ((3909426288881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT205 (i+1))
      = (∑ i ∈ Finset.range 111, stT205 (i+1)) + stT205 112 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 111
    simpa using h
  have hprev := st205_p111
  have hstep := st205_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p113 : ((3883308111037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT205 (i+1))
      = (∑ i ∈ Finset.range 112, stT205 (i+1)) + stT205 113 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 112
    simpa using h
  have hprev := st205_p112
  have hstep := st205_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p114 : ((53666628391/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT205 (i+1))
      = (∑ i ∈ Finset.range 113, stT205 (i+1)) + stT205 114 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 113
    simpa using h
  have hprev := st205_p113
  have hstep := st205_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p115 : ((14306469899/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT205 (i+1))
      = (∑ i ∈ Finset.range 114, stT205 (i+1)) + stT205 115 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 114
    simpa using h
  have hprev := st205_p114
  have hstep := st205_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p116 : ((2006550645319/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT205 (i+1))
      = (∑ i ∈ Finset.range 115, stT205 (i+1)) + stT205 116 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 115
    simpa using h
  have hprev := st205_p115
  have hstep := st205_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p117 : ((3649989655373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT205 (i+1))
      = (∑ i ∈ Finset.range 116, stT205 (i+1)) + stT205 117 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 116
    simpa using h
  have hprev := st205_p116
  have hstep := st205_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p118 : ((6863905694971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT205 (i+1))
      = (∑ i ∈ Finset.range 117, stT205 (i+1)) + stT205 118 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 117
    simpa using h
  have hprev := st205_p117
  have hstep := st205_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p119 : ((7729818625771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT205 (i+1))
      = (∑ i ∈ Finset.range 118, stT205 (i+1)) + stT205 119 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 118
    simpa using h
  have hprev := st205_p118
  have hstep := st205_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p120 : ((7901785989241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT205 (i+1))
      = (∑ i ∈ Finset.range 119, stT205 (i+1)) + stT205 120 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 119
    simpa using h
  have hprev := st205_p119
  have hstep := st205_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p121 : ((6994236807577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT205 (i+1))
      = (∑ i ∈ Finset.range 120, stT205 (i+1)) + stT205 121 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 120
    simpa using h
  have hprev := st205_p120
  have hstep := st205_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p122 : ((7046084792253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT205 (i+1))
      = (∑ i ∈ Finset.range 121, stT205 (i+1)) + stT205 122 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 121
    simpa using h
  have hprev := st205_p121
  have hstep := st205_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p123 : ((793618808399/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT205 (i+1))
      = (∑ i ∈ Finset.range 122, stT205 (i+1)) + stT205 123 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 122
    simpa using h
  have hprev := st205_p122
  have hstep := st205_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p124 : ((7714699602737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT205 (i+1))
      = (∑ i ∈ Finset.range 123, stT205 (i+1)) + stT205 124 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 123
    simpa using h
  have hprev := st205_p123
  have hstep := st205_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p125 : ((6867039454001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT205 (i+1))
      = (∑ i ∈ Finset.range 124, stT205 (i+1)) + stT205 125 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 124
    simpa using h
  have hprev := st205_p124
  have hstep := st205_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p126 : ((7203755351811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT205 (i+1))
      = (∑ i ∈ Finset.range 125, stT205 (i+1)) + stT205 126 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 125
    simpa using h
  have hprev := st205_p125
  have hstep := st205_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p127 : ((8007528628103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT205 (i+1))
      = (∑ i ∈ Finset.range 126, stT205 (i+1)) + stT205 127 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 126
    simpa using h
  have hprev := st205_p126
  have hstep := st205_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p128 : ((7603676725199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT205 (i+1))
      = (∑ i ∈ Finset.range 127, stT205 (i+1)) + stT205 128 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 127
    simpa using h
  have hprev := st205_p127
  have hstep := st205_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p129 : ((6830547419393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT205 (i+1))
      = (∑ i ∈ Finset.range 128, stT205 (i+1)) + stT205 129 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 128
    simpa using h
  have hprev := st205_p128
  have hstep := st205_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p130 : ((7259601561819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT205 (i+1))
      = (∑ i ∈ Finset.range 129, stT205 (i+1)) + stT205 130 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 129
    simpa using h
  have hprev := st205_p129
  have hstep := st205_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p131 : ((8021512513907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT205 (i+1))
      = (∑ i ∈ Finset.range 130, stT205 (i+1)) + stT205 131 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 130
    simpa using h
  have hprev := st205_p130
  have hstep := st205_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p132 : ((1901146652157/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT205 (i+1))
      = (∑ i ∈ Finset.range 131, stT205 (i+1)) + stT205 132 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 131
    simpa using h
  have hprev := st205_p131
  have hstep := st205_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p133 : ((854220713211/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT205 (i+1))
      = (∑ i ∈ Finset.range 132, stT205 (i+1)) + stT205 133 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 132
    simpa using h
  have hprev := st205_p132
  have hstep := st205_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p134 : ((450136002261/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT205 (i+1))
      = (∑ i ∈ Finset.range 133, stT205 (i+1)) + stT205 134 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 133
    simpa using h
  have hprev := st205_p133
  have hstep := st205_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p135 : ((3998425109987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT205 (i+1))
      = (∑ i ∈ Finset.range 134, stT205 (i+1)) + stT205 135 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 134
    simpa using h
  have hprev := st205_p134
  have hstep := st205_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p136 : ((482123455261/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT205 (i+1))
      = (∑ i ∈ Finset.range 135, stT205 (i+1)) + stT205 136 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 135
    simpa using h
  have hprev := st205_p135
  have hstep := st205_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p137 : ((107654514013/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT205 (i+1))
      = (∑ i ∈ Finset.range 136, stT205 (i+1)) + stT205 137 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 136
    simpa using h
  have hprev := st205_p136
  have hstep := st205_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p138 : ((44052178117/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT205 (i+1))
      = (∑ i ∈ Finset.range 137, stT205 (i+1)) + stT205 138 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 137
    simpa using h
  have hprev := st205_p137
  have hstep := st205_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p139 : ((986566843467/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT205 (i+1))
      = (∑ i ∈ Finset.range 138, stT205 (i+1)) + stT205 139 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 138
    simpa using h
  have hprev := st205_p138
  have hstep := st205_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p140 : ((246761828379/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT205 (i+1))
      = (∑ i ∈ Finset.range 139, stT205 (i+1)) + stT205 140 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 139
    simpa using h
  have hprev := st205_p139
  have hstep := st205_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p141 : ((55155278623/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT205 (i+1))
      = (∑ i ∈ Finset.range 140, stT205 (i+1)) + stT205 141 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 140
    simpa using h
  have hprev := st205_p140
  have hstep := st205_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p142 : ((686170535199/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT205 (i+1))
      = (∑ i ∈ Finset.range 141, stT205 (i+1)) + stT205 142 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 141
    simpa using h
  have hprev := st205_p141
  have hstep := st205_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p143 : ((3820576570159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT205 (i+1))
      = (∑ i ∈ Finset.range 142, stT205 (i+1)) + stT205 143 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 142
    simpa using h
  have hprev := st205_p142
  have hstep := st205_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p144 : ((2012484494201/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT205 (i+1))
      = (∑ i ∈ Finset.range 143, stT205 (i+1)) + stT205 144 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 143
    simpa using h
  have hprev := st205_p143
  have hstep := st205_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p145 : ((462270419259/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT205 (i+1))
      = (∑ i ∈ Finset.range 144, stT205 (i+1)) + stT205 145 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 144
    simpa using h
  have hprev := st205_p144
  have hstep := st205_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p146 : ((424212957349/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT205 (i+1))
      = (∑ i ∈ Finset.range 145, stT205 (i+1)) + stT205 146 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 145
    simpa using h
  have hprev := st205_p145
  have hstep := st205_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p147 : ((3617123752437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT205 (i+1))
      = (∑ i ∈ Finset.range 146, stT205 (i+1)) + stT205 147 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 146
    simpa using h
  have hprev := st205_p146
  have hstep := st205_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p148 : ((999245391183/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT205 (i+1))
      = (∑ i ∈ Finset.range 147, stT205 (i+1)) + stT205 148 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 147
    simpa using h
  have hprev := st205_p147
  have hstep := st205_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p149 : ((978762133487/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT205 (i+1))
      = (∑ i ∈ Finset.range 148, stT205 (i+1)) + stT205 149 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 148
    simpa using h
  have hprev := st205_p148
  have hstep := st205_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p150 : ((175339021901/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT205 (i+1))
      = (∑ i ∈ Finset.range 149, stT205 (i+1)) + stT205 150 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 149
    simpa using h
  have hprev := st205_p149
  have hstep := st205_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p151 : ((6846350836421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT205 (i+1))
      = (∑ i ∈ Finset.range 150, stT205 (i+1)) + stT205 151 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 150
    simpa using h
  have hprev := st205_p150
  have hstep := st205_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p152 : ((7585412068253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT205 (i+1))
      = (∑ i ∈ Finset.range 151, stT205 (i+1)) + stT205 152 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 151
    simpa using h
  have hprev := st205_p151
  have hstep := st205_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p153 : ((8075328321089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT205 (i+1))
      = (∑ i ∈ Finset.range 152, stT205 (i+1)) + stT205 153 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 152
    simpa using h
  have hprev := st205_p152
  have hstep := st205_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p154 : ((236431778559/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT205 (i+1))
      = (∑ i ∈ Finset.range 153, stT205 (i+1)) + stT205 154 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 153
    simpa using h
  have hprev := st205_p153
  have hstep := st205_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p155 : ((1709808635937/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT205 (i+1))
      = (∑ i ∈ Finset.range 154, stT205 (i+1)) + stT205 155 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 154
    simpa using h
  have hprev := st205_p154
  have hstep := st205_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p156 : ((1747215737697/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT205 (i+1))
      = (∑ i ∈ Finset.range 155, stT205 (i+1)) + stT205 156 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 155
    simpa using h
  have hprev := st205_p155
  have hstep := st205_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p157 : ((486549532651/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT205 (i+1))
      = (∑ i ∈ Finset.range 156, stT205 (i+1)) + stT205 157 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 156
    simpa using h
  have hprev := st205_p156
  have hstep := st205_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p158 : ((8051602451291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT205 (i+1))
      = (∑ i ∈ Finset.range 157, stT205 (i+1)) + stT205 158 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 157
    simpa using h
  have hprev := st205_p157
  have hstep := st205_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p159 : ((1481173875383/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT205 (i+1))
      = (∑ i ∈ Finset.range 158, stT205 (i+1)) + stT205 159 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 158
    simpa using h
  have hprev := st205_p158
  have hstep := st205_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p160 : ((54272865663/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT205 (i+1))
      = (∑ i ∈ Finset.range 159, stT205 (i+1)) + stT205 160 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 159
    simpa using h
  have hprev := st205_p159
  have hstep := st205_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p161 : ((282828806863/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT205 (i+1))
      = (∑ i ∈ Finset.range 160, stT205 (i+1)) + stT205 161 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 160
    simpa using h
  have hprev := st205_p160
  have hstep := st205_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p162 : ((7854385203157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT205 (i+1))
      = (∑ i ∈ Finset.range 161, stT205 (i+1)) + stT205 162 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 161
    simpa using h
  have hprev := st205_p161
  have hstep := st205_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p163 : ((8039330904137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT205 (i+1))
      = (∑ i ∈ Finset.range 162, stT205 (i+1)) + stT205 163 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 162
    simpa using h
  have hprev := st205_p162
  have hstep := st205_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p164 : ((3687898030473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT205 (i+1))
      = (∑ i ∈ Finset.range 163, stT205 (i+1)) + stT205 164 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 163
    simpa using h
  have hprev := st205_p163
  have hstep := st205_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p165 : ((211741775523/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT205 (i+1))
      = (∑ i ∈ Finset.range 164, stT205 (i+1)) + stT205 165 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 164
    simpa using h
  have hprev := st205_p164
  have hstep := st205_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p166 : ((3524074583793/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT205 (i+1))
      = (∑ i ∈ Finset.range 165, stT205 (i+1)) + stT205 166 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 165
    simpa using h
  have hprev := st205_p165
  have hstep := st205_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p167 : ((7821791866827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT205 (i+1))
      = (∑ i ∈ Finset.range 166, stT205 (i+1)) + stT205 167 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 166
    simpa using h
  have hprev := st205_p166
  have hstep := st205_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p168 : ((1614030579387/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT205 (i+1))
      = (∑ i ∈ Finset.range 167, stT205 (i+1)) + stT205 168 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 167
    simpa using h
  have hprev := st205_p167
  have hstep := st205_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p169 : ((7472932717769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT205 (i+1))
      = (∑ i ∈ Finset.range 168, stT205 (i+1)) + stT205 169 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 168
    simpa using h
  have hprev := st205_p168
  have hstep := st205_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p170 : ((3405087242677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT205 (i+1))
      = (∑ i ∈ Finset.range 169, stT205 (i+1)) + stT205 170 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 169
    simpa using h
  have hprev := st205_p169
  have hstep := st205_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p171 : ((693123256193/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT205 (i+1))
      = (∑ i ∈ Finset.range 170, stT205 (i+1)) + stT205 171 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 170
    simpa using h
  have hprev := st205_p170
  have hstep := st205_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p172 : ((3837948368239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT205 (i+1))
      = (∑ i ∈ Finset.range 171, stT205 (i+1)) + stT205 172 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 171
    simpa using h
  have hprev := st205_p171
  have hstep := st205_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p173 : ((253262910309/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT205 (i+1))
      = (∑ i ∈ Finset.range 172, stT205 (i+1)) + stT205 173 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 172
    simpa using h
  have hprev := st205_p172
  have hstep := st205_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p174 : ((7687189554743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT205 (i+1))
      = (∑ i ∈ Finset.range 173, stT205 (i+1)) + stT205 174 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 173
    simpa using h
  have hprev := st205_p173
  have hstep := st205_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p175 : ((69443630721/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT205 (i+1))
      = (∑ i ∈ Finset.range 174, stT205 (i+1)) + stT205 175 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 174
    simpa using h
  have hprev := st205_p174
  have hstep := st205_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p176 : ((3391393764167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT205 (i+1))
      = (∑ i ∈ Finset.range 175, stT205 (i+1)) + stT205 176 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 175
    simpa using h
  have hprev := st205_p175
  have hstep := st205_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p177 : ((1848045191151/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT205 (i+1))
      = (∑ i ∈ Finset.range 176, stT205 (i+1)) + stT205 177 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 176
    simpa using h
  have hprev := st205_p176
  have hstep := st205_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p178 : ((4019489773341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT205 (i+1))
      = (∑ i ∈ Finset.range 177, stT205 (i+1)) + stT205 178 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 177
    simpa using h
  have hprev := st205_p177
  have hstep := st205_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p179 : ((3979441778743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT205 (i+1))
      = (∑ i ∈ Finset.range 178, stT205 (i+1)) + stT205 179 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 178
    simpa using h
  have hprev := st205_p178
  have hstep := st205_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p180 : ((725166295187/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT205 (i+1))
      = (∑ i ∈ Finset.range 179, stT205 (i+1)) + stT205 180 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 179
    simpa using h
  have hprev := st205_p179
  have hstep := st205_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p181 : ((134829067423/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT205 (i+1))
      = (∑ i ∈ Finset.range 180, stT205 (i+1)) + stT205 181 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 180
    simpa using h
  have hprev := st205_p180
  have hstep := st205_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p182 : ((70115274443/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT205 (i+1))
      = (∑ i ∈ Finset.range 181, stT205 (i+1)) + stT205 182 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 181
    simpa using h
  have hprev := st205_p181
  have hstep := st205_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p183 : ((309946405799/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT205 (i+1))
      = (∑ i ∈ Finset.range 182, stT205 (i+1)) + stT205 183 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 182
    simpa using h
  have hprev := st205_p182
  have hstep := st205_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p184 : ((2030030701067/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT205 (i+1))
      = (∑ i ∈ Finset.range 183, stT205 (i+1)) + stT205 184 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 183
    simpa using h
  have hprev := st205_p183
  have hstep := st205_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p185 : ((3857669211289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT205 (i+1))
      = (∑ i ∈ Finset.range 184, stT205 (i+1)) + stT205 185 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 184
    simpa using h
  have hprev := st205_p184
  have hstep := st205_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p186 : ((698710455857/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT205 (i+1))
      = (∑ i ∈ Finset.range 185, stT205 (i+1)) + stT205 186 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 185
    simpa using h
  have hprev := st205_p185
  have hstep := st205_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p187 : ((3366686651607/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT205 (i+1))
      = (∑ i ∈ Finset.range 186, stT205 (i+1)) + stT205 187 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 186
    simpa using h
  have hprev := st205_p186
  have hstep := st205_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p188 : ((3612296719143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT205 (i+1))
      = (∑ i ∈ Finset.range 187, stT205 (i+1)) + stT205 188 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 187
    simpa using h
  have hprev := st205_p187
  have hstep := st205_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p189 : ((3964141321287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT205 (i+1))
      = (∑ i ∈ Finset.range 188, stT205 (i+1)) + stT205 189 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 188
    simpa using h
  have hprev := st205_p188
  have hstep := st205_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p190 : ((4047957014519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT205 (i+1))
      = (∑ i ∈ Finset.range 189, stT205 (i+1)) + stT205 190 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 189
    simpa using h
  have hprev := st205_p189
  have hstep := st205_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p191 : ((7555671950363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT205 (i+1))
      = (∑ i ∈ Finset.range 190, stT205 (i+1)) + stT205 191 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 190
    simpa using h
  have hprev := st205_p190
  have hstep := st205_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p192 : ((6875888764083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT205 (i+1))
      = (∑ i ∈ Finset.range 191, stT205 (i+1)) + stT205 192 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 191
    simpa using h
  have hprev := st205_p191
  have hstep := st205_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p193 : ((6758853160827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT205 (i+1))
      = (∑ i ∈ Finset.range 192, stT205 (i+1)) + stT205 193 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 192
    simpa using h
  have hprev := st205_p192
  have hstep := st205_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p194 : ((7319502255279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT205 (i+1))
      = (∑ i ∈ Finset.range 193, stT205 (i+1)) + stT205 194 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 193
    simpa using h
  have hprev := st205_p193
  have hstep := st205_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p195 : ((7984664744179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT205 (i+1))
      = (∑ i ∈ Finset.range 194, stT205 (i+1)) + stT205 195 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 194
    simpa using h
  have hprev := st205_p194
  have hstep := st205_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p196 : ((8086307499679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT205 (i+1))
      = (∑ i ∈ Finset.range 195, stT205 (i+1)) + stT205 196 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 195
    simpa using h
  have hprev := st205_p195
  have hstep := st205_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p197 : ((1505596775071/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT205 (i+1))
      = (∑ i ∈ Finset.range 196, stT205 (i+1)) + stT205 197 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 196
    simpa using h
  have hprev := st205_p196
  have hstep := st205_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p198 : ((274590356609/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT205 (i+1))
      = (∑ i ∈ Finset.range 197, stT205 (i+1)) + stT205 198 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 197
    simpa using h
  have hprev := st205_p197
  have hstep := st205_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p199 : ((6744487868459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT205 (i+1))
      = (∑ i ∈ Finset.range 198, stT205 (i+1)) + stT205 199 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 198
    simpa using h
  have hprev := st205_p198
  have hstep := st205_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p200 : ((7278999193343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT205 (i+1))
      = (∑ i ∈ Finset.range 199, stT205 (i+1)) + stT205 200 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 199
    simpa using h
  have hprev := st205_p199
  have hstep := st205_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p201 : ((1987737055907/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT205 (i+1))
      = (∑ i ∈ Finset.range 200, stT205 (i+1)) + stT205 201 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 200
    simpa using h
  have hprev := st205_p200
  have hstep := st205_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p202 : ((1015167464539/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT205 (i+1))
      = (∑ i ∈ Finset.range 201, stT205 (i+1)) + stT205 202 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 201
    simpa using h
  have hprev := st205_p201
  have hstep := st205_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p203 : ((3816937403461/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT205 (i+1))
      = (∑ i ∈ Finset.range 202, stT205 (i+1)) + stT205 203 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 202
    simpa using h
  have hprev := st205_p202
  have hstep := st205_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p204 : ((6948255431403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT205 (i+1))
      = (∑ i ∈ Finset.range 203, stT205 (i+1)) + stT205 204 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 203
    simpa using h
  have hprev := st205_p203
  have hstep := st205_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p205 : ((6699519008787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT205 (i+1))
      = (∑ i ∈ Finset.range 204, stT205 (i+1)) + stT205 205 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 204
    simpa using h
  have hprev := st205_p204
  have hstep := st205_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p206 : ((3555962861241/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT205 (i+1))
      = (∑ i ∈ Finset.range 205, stT205 (i+1)) + stT205 206 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 205
    simpa using h
  have hprev := st205_p205
  have hstep := st205_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p207 : ((3902935688177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT205 (i+1))
      = (∑ i ∈ Finset.range 206, stT205 (i+1)) + stT205 207 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 206
    simpa using h
  have hprev := st205_p206
  have hstep := st205_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p208 : ((2038702392901/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT205 (i+1))
      = (∑ i ∈ Finset.range 207, stT205 (i+1)) + stT205 208 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 207
    simpa using h
  have hprev := st205_p207
  have hstep := st205_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p209 : ((3925143788287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT205 (i+1))
      = (∑ i ∈ Finset.range 208, stT205 (i+1)) + stT205 209 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 208
    simpa using h
  have hprev := st205_p208
  have hstep := st205_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p210 : ((716660192681/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT205 (i+1))
      = (∑ i ∈ Finset.range 209, stT205 (i+1)) + stT205 210 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 209
    simpa using h
  have hprev := st205_p209
  have hstep := st205_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p211 : ((1341148691839/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT205 (i+1))
      = (∑ i ∈ Finset.range 210, stT205 (i+1)) + stT205 211 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 210
    simpa using h
  have hprev := st205_p210
  have hstep := st205_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p212 : ((6866214059693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT205 (i+1))
      = (∑ i ∈ Finset.range 211, stT205 (i+1)) + stT205 212 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 211
    simpa using h
  have hprev := st205_p211
  have hstep := st205_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p213 : ((7504947683669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT205 (i+1))
      = (∑ i ∈ Finset.range 212, stT205 (i+1)) + stT205 213 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 212
    simpa using h
  have hprev := st205_p212
  have hstep := st205_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p214 : ((2018233760561/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT205 (i+1))
      = (∑ i ∈ Finset.range 213, stT205 (i+1)) + stT205 214 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 213
    simpa using h
  have hprev := st205_p213
  have hstep := st205_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p215 : ((4045006426999/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT205 (i+1))
      = (∑ i ∈ Finset.range 214, stT205 (i+1)) + stT205 215 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 214
    simpa using h
  have hprev := st205_p214
  have hstep := st205_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p216 : ((117907814197/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT205 (i+1))
      = (∑ i ∈ Finset.range 215, stT205 (i+1)) + stT205 216 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 215
    simpa using h
  have hprev := st205_p215
  have hstep := st205_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p217 : ((3448998641639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT205 (i+1))
      = (∑ i ∈ Finset.range 216, stT205 (i+1)) + stT205 217 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 216
    simpa using h
  have hprev := st205_p216
  have hstep := st205_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p218 : ((668105715919/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT205 (i+1))
      = (∑ i ∈ Finset.range 217, stT205 (i+1)) + stT205 218 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 217
    simpa using h
  have hprev := st205_p217
  have hstep := st205_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p219 : ((7069360641659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT205 (i+1))
      = (∑ i ∈ Finset.range 218, stT205 (i+1)) + stT205 219 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 218
    simpa using h
  have hprev := st205_p218
  have hstep := st205_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p220 : ((1935830412353/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT205 (i+1))
      = (∑ i ∈ Finset.range 219, stT205 (i+1)) + stT205 220 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 219
    simpa using h
  have hprev := st205_p219
  have hstep := st205_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p221 : ((2039686260449/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT205 (i+1))
      = (∑ i ∈ Finset.range 220, stT205 (i+1)) + stT205 221 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 220
    simpa using h
  have hprev := st205_p220
  have hstep := st205_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p222 : ((7986314741141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT205 (i+1))
      = (∑ i ∈ Finset.range 221, stT205 (i+1)) + stT205 222 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 221
    simpa using h
  have hprev := st205_p221
  have hstep := st205_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p223 : ((7366830901241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT205 (i+1))
      = (∑ i ∈ Finset.range 222, stT205 (i+1)) + stT205 223 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 222
    simpa using h
  have hprev := st205_p222
  have hstep := st205_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p224 : ((6789488383997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT205 (i+1))
      = (∑ i ∈ Finset.range 223, stT205 (i+1)) + stT205 224 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 223
    simpa using h
  have hprev := st205_p223
  have hstep := st205_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p225 : ((1675744918519/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT205 (i+1))
      = (∑ i ∈ Finset.range 224, stT205 (i+1)) + stT205 225 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 224
    simpa using h
  have hprev := st205_p224
  have hstep := st205_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p226 : ((1792572238219/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT205 (i+1))
      = (∑ i ∈ Finset.range 225, stT205 (i+1)) + stT205 226 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 225
    simpa using h
  have hprev := st205_p225
  have hstep := st205_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p227 : ((7829723638573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT205 (i+1))
      = (∑ i ∈ Finset.range 226, stT205 (i+1)) + stT205 227 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 226
    simpa using h
  have hprev := st205_p226
  have hstep := st205_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p228 : ((8179458365981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT205 (i+1))
      = (∑ i ∈ Finset.range 227, stT205 (i+1)) + stT205 228 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 227
    simpa using h
  have hprev := st205_p227
  have hstep := st205_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p229 : ((159171605521/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT205 (i+1))
      = (∑ i ∈ Finset.range 228, stT205 (i+1)) + stT205 229 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 228
    simpa using h
  have hprev := st205_p228
  have hstep := st205_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p230 : ((7336210990961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT205 (i+1))
      = (∑ i ∈ Finset.range 229, stT205 (i+1)) + stT205 230 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 229
    simpa using h
  have hprev := st205_p229
  have hstep := st205_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p231 : ((6776146457713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT205 (i+1))
      = (∑ i ∈ Finset.range 230, stT205 (i+1)) + stT205 231 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 230
    simpa using h
  have hprev := st205_p230
  have hstep := st205_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p232 : ((66892470933/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT205 (i+1))
      = (∑ i ∈ Finset.range 231, stT205 (i+1)) + stT205 232 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 231
    simpa using h
  have hprev := st205_p231
  have hstep := st205_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p233 : ((285412104167/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT205 (i+1))
      = (∑ i ∈ Finset.range 232, stT205 (i+1)) + stT205 233 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 232
    simpa using h
  have hprev := st205_p232
  have hstep := st205_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p234 : ((1557591669603/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT205 (i+1))
      = (∑ i ∈ Finset.range 233, stT205 (i+1)) + stT205 234 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 233
    simpa using h
  have hprev := st205_p233
  have hstep := st205_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p235 : ((8177708672143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT205 (i+1))
      = (∑ i ∈ Finset.range 234, stT205 (i+1)) + stT205 235 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 234
    simpa using h
  have hprev := st205_p234
  have hstep := st205_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p236 : ((4014612431459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT205 (i+1))
      = (∑ i ∈ Finset.range 235, stT205 (i+1)) + stT205 236 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 235
    simpa using h
  have hprev := st205_p235
  have hstep := st205_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p237 : ((3725606396629/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT205 (i+1))
      = (∑ i ∈ Finset.range 236, stT205 (i+1)) + stT205 237 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 236
    simpa using h
  have hprev := st205_p236
  have hstep := st205_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p238 : ((3425731345231/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT205 (i+1))
      = (∑ i ∈ Finset.range 237, stT205 (i+1)) + stT205 238 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 237
    simpa using h
  have hprev := st205_p237
  have hstep := st205_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p239 : ((6646716856399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT205 (i+1))
      = (∑ i ∈ Finset.range 238, stT205 (i+1)) + stT205 239 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 238
    simpa using h
  have hprev := st205_p238
  have hstep := st205_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p240 : ((871899751907/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT205 (i+1))
      = (∑ i ∈ Finset.range 239, stT205 (i+1)) + stT205 240 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 239
    simpa using h
  have hprev := st205_p239
  have hstep := st205_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p241 : ((1902098425229/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT205 (i+1))
      = (∑ i ∈ Finset.range 240, stT205 (i+1)) + stT205 241 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 240
    simpa using h
  have hprev := st205_p240
  have hstep := st205_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p242 : ((2028612134551/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT205 (i+1))
      = (∑ i ∈ Finset.range 241, stT205 (i+1)) + stT205 242 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 241
    simpa using h
  have hprev := st205_p241
  have hstep := st205_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p243 : ((2038386990801/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT205 (i+1))
      = (∑ i ∈ Finset.range 242, stT205 (i+1)) + stT205 243 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 242
    simpa using h
  have hprev := st205_p242
  have hstep := st205_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p244 : ((3851448707337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT205 (i+1))
      = (∑ i ∈ Finset.range 243, stT205 (i+1)) + stT205 244 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 243
    simpa using h
  have hprev := st205_p243
  have hstep := st205_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p245 : ((220773118443/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT205 (i+1))
      = (∑ i ∈ Finset.range 244, stT205 (i+1)) + stT205 245 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 244
    simpa using h
  have hprev := st205_p244
  have hstep := st205_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p246 : ((832526879479/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT205 (i+1))
      = (∑ i ∈ Finset.range 245, stT205 (i+1)) + stT205 246 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 245
    simpa using h
  have hprev := st205_p245
  have hstep := st205_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p247 : ((1687933418101/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT205 (i+1))
      = (∑ i ∈ Finset.range 246, stT205 (i+1)) + stT205 247 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 246
    simpa using h
  have hprev := st205_p246
  have hstep := st205_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p248 : ((1819114893101/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT205 (i+1))
      = (∑ i ∈ Finset.range 247, stT205 (i+1)) + stT205 248 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 247
    simpa using h
  have hprev := st205_p247
  have hstep := st205_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p249 : ((197348039521/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT205 (i+1))
      = (∑ i ∈ Finset.range 248, stT205 (i+1)) + stT205 249 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 248
    simpa using h
  have hprev := st205_p248
  have hstep := st205_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p250 : ((328376794409/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT205 (i+1))
      = (∑ i ∈ Finset.range 249, stT205 (i+1)) + stT205 250 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 249
    simpa using h
  have hprev := st205_p249
  have hstep := st205_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p251 : ((100315630179/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT205 (i+1))
      = (∑ i ∈ Finset.range 250, stT205 (i+1)) + stT205 251 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 250
    simpa using h
  have hprev := st205_p250
  have hstep := st205_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p252 : ((7460663903247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT205 (i+1))
      = (∑ i ∈ Finset.range 251, stT205 (i+1)) + stT205 252 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 251
    simpa using h
  have hprev := st205_p251
  have hstep := st205_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p253 : ((3435266841621/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT205 (i+1))
      = (∑ i ∈ Finset.range 252, stT205 (i+1)) + stT205 253 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 252
    simpa using h
  have hprev := st205_p252
  have hstep := st205_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p254 : ((3310227409941/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT205 (i+1))
      = (∑ i ∈ Finset.range 253, stT205 (i+1)) + stT205 254 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 253
    simpa using h
  have hprev := st205_p253
  have hstep := st205_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p255 : ((3430877291341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT205 (i+1))
      = (∑ i ∈ Finset.range 254, stT205 (i+1)) + stT205 255 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 254
    simpa using h
  have hprev := st205_p254
  have hstep := st205_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p256 : ((3721892603841/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT205 (i+1))
      = (∑ i ∈ Finset.range 255, stT205 (i+1)) + stT205 256 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 255
    simpa using h
  have hprev := st205_p255
  have hstep := st205_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p257 : ((400584409617/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT205 (i+1))
      = (∑ i ∈ Finset.range 256, stT205 (i+1)) + stT205 257 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 256
    simpa using h
  have hprev := st205_p256
  have hstep := st205_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p258 : ((128502191637/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT205 (i+1))
      = (∑ i ∈ Finset.range 257, stT205 (i+1)) + stT205 258 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 257
    simpa using h
  have hprev := st205_p257
  have hstep := st205_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p259 : ((3978389522639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT205 (i+1))
      = (∑ i ∈ Finset.range 258, stT205 (i+1)) + stT205 259 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 258
    simpa using h
  have hprev := st205_p258
  have hstep := st205_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p260 : ((3685633285069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT205 (i+1))
      = (∑ i ∈ Finset.range 259, stT205 (i+1)) + stT205 260 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 259
    simpa using h
  have hprev := st205_p259
  have hstep := st205_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p261 : ((1703527995447/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT205 (i+1))
      = (∑ i ∈ Finset.range 260, stT205 (i+1)) + stT205 261 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 260
    simpa using h
  have hprev := st205_p260
  have hstep := st205_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p262 : ((1322080636159/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT205 (i+1))
      = (∑ i ∈ Finset.range 261, stT205 (i+1)) + stT205 262 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 261
    simpa using h
  have hprev := st205_p261
  have hstep := st205_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p263 : ((6875793461561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT205 (i+1))
      = (∑ i ∈ Finset.range 262, stT205 (i+1)) + stT205 263 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 262
    simpa using h
  have hprev := st205_p262
  have hstep := st205_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p264 : ((7454364892637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT205 (i+1))
      = (∑ i ∈ Finset.range 263, stT205 (i+1)) + stT205 264 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 263
    simpa using h
  have hprev := st205_p263
  have hstep := st205_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p265 : ((250419241531/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT205 (i+1))
      = (∑ i ∈ Finset.range 264, stT205 (i+1)) + stT205 265 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 264
    simpa using h
  have hprev := st205_p264
  have hstep := st205_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p266 : ((1647185632813/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT205 (i+1))
      = (∑ i ∈ Finset.range 265, stT205 (i+1)) + stT205 266 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 265
    simpa using h
  have hprev := st205_p265
  have hstep := st205_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p267 : ((799882755089/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT205 (i+1))
      = (∑ i ∈ Finset.range 266, stT205 (i+1)) + stT205 267 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 266
    simpa using h
  have hprev := st205_p266
  have hstep := st205_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p268 : ((3718883053141/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT205 (i+1))
      = (∑ i ∈ Finset.range 267, stT205 (i+1)) + stT205 268 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 267
    simpa using h
  have hprev := st205_p267
  have hstep := st205_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p269 : ((3433216377733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT205 (i+1))
      = (∑ i ∈ Finset.range 268, stT205 (i+1)) + stT205 269 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 268
    simpa using h
  have hprev := st205_p268
  have hstep := st205_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p270 : ((412493283431/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT205 (i+1))
      = (∑ i ∈ Finset.range 269, stT205 (i+1)) + stT205 270 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 269
    simpa using h
  have hprev := st205_p269
  have hstep := st205_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p271 : ((423877122769/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT205 (i+1))
      = (∑ i ∈ Finset.range 270, stT205 (i+1)) + stT205 271 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 270
    simpa using h
  have hprev := st205_p270
  have hstep := st205_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p272 : ((456927448981/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT205 (i+1))
      = (∑ i ∈ Finset.range 271, stT205 (i+1)) + stT205 272 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 271
    simpa using h
  have hprev := st205_p271
  have hstep := st205_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p273 : ((7898526100009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT205 (i+1))
      = (∑ i ∈ Finset.range 272, stT205 (i+1)) + stT205 273 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 272
    simpa using h
  have hprev := st205_p272
  have hstep := st205_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p274 : ((1645924603139/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT205 (i+1))
      = (∑ i ∈ Finset.range 273, stT205 (i+1)) + stT205 274 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 273
    simpa using h
  have hprev := st205_p273
  have hstep := st205_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p275 : ((8129540494431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT205 (i+1))
      = (∑ i ∈ Finset.range 274, stT205 (i+1)) + stT205 275 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 274
    simpa using h
  have hprev := st205_p274
  have hstep := st205_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p276 : ((7653989911441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT205 (i+1))
      = (∑ i ∈ Finset.range 275, stT205 (i+1)) + stT205 276 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 275
    simpa using h
  have hprev := st205_p275
  have hstep := st205_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p277 : ((7055108458887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT205 (i+1))
      = (∑ i ∈ Finset.range 276, stT205 (i+1)) + stT205 277 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 276
    simpa using h
  have hprev := st205_p276
  have hstep := st205_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p278 : ((1329196058643/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT205 (i+1))
      = (∑ i ∈ Finset.range 277, stT205 (i+1)) + stT205 278 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 277
    simpa using h
  have hprev := st205_p277
  have hstep := st205_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p279 : ((1327446701073/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT205 (i+1))
      = (∑ i ∈ Finset.range 278, stT205 (i+1)) + stT205 279 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 278
    simpa using h
  have hprev := st205_p278
  have hstep := st205_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p280 : ((7030770690961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT205 (i+1))
      = (∑ i ∈ Finset.range 279, stT205 (i+1)) + stT205 280 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 279
    simpa using h
  have hprev := st205_p279
  have hstep := st205_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p281 : ((381146186069/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT205 (i+1))
      = (∑ i ∈ Finset.range 280, stT205 (i+1)) + stT205 281 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 280
    simpa using h
  have hprev := st205_p280
  have hstep := st205_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p282 : ((811194688549/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT205 (i+1))
      = (∑ i ∈ Finset.range 281, stT205 (i+1)) + stT205 282 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 281
    simpa using h
  have hprev := st205_p281
  have hstep := st205_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p283 : ((4126018450037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT205 (i+1))
      = (∑ i ∈ Finset.range 282, stT205 (i+1)) + stT205 283 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 282
    simpa using h
  have hprev := st205_p282
  have hstep := st205_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p284 : ((1595055986213/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT205 (i+1))
      = (∑ i ∈ Finset.range 283, stT205 (i+1)) + stT205 284 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 283
    simpa using h
  have hprev := st205_p283
  have hstep := st205_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p285 : ((7421940666809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT205 (i+1))
      = (∑ i ∈ Finset.range 284, stT205 (i+1)) + stT205 285 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 284
    simpa using h
  have hprev := st205_p284
  have hstep := st205_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p286 : ((6867052547609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT205 (i+1))
      = (∑ i ∈ Finset.range 285, stT205 (i+1)) + stT205 286 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 285
    simpa using h
  have hprev := st205_p285
  have hstep := st205_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p287 : ((263313577531/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT205 (i+1))
      = (∑ i ∈ Finset.range 286, stT205 (i+1)) + stT205 287 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 286
    simpa using h
  have hprev := st205_p286
  have hstep := st205_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p288 : ((1341214302987/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT205 (i+1))
      = (∑ i ∈ Finset.range 287, stT205 (i+1)) + stT205 288 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 287
    simpa using h
  have hprev := st205_p287
  have hstep := st205_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p289 : ((286980357111/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT205 (i+1))
      = (∑ i ∈ Finset.range 288, stT205 (i+1)) + stT205 289 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 288
    simpa using h
  have hprev := st205_p288
  have hstep := st205_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p290 : ((1552138027119/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT205 (i+1))
      = (∑ i ∈ Finset.range 289, stT205 (i+1)) + stT205 290 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 289
    simpa using h
  have hprev := st205_p289
  have hstep := st205_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p291 : ((1636764006171/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT205 (i+1))
      = (∑ i ∈ Finset.range 290, stT205 (i+1)) + stT205 291 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 290
    simpa using h
  have hprev := st205_p290
  have hstep := st205_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p292 : ((824408151573/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT205 (i+1))
      = (∑ i ∈ Finset.range 291, stT205 (i+1)) + stT205 292 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 291
    simpa using h
  have hprev := st205_p291
  have hstep := st205_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p293 : ((3957660097447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT205 (i+1))
      = (∑ i ∈ Finset.range 292, stT205 (i+1)) + stT205 293 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 292
    simpa using h
  have hprev := st205_p292
  have hstep := st205_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p294 : ((3676972409299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT205 (i+1))
      = (∑ i ∈ Finset.range 293, stT205 (i+1)) + stT205 294 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 293
    simpa using h
  have hprev := st205_p293
  have hstep := st205_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p295 : ((341131395219/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT205 (i+1))
      = (∑ i ∈ Finset.range 294, stT205 (i+1)) + stT205 295 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 294
    simpa using h
  have hprev := st205_p294
  have hstep := st205_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p296 : ((3283412891479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT205 (i+1))
      = (∑ i ∈ Finset.range 295, stT205 (i+1)) + stT205 296 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 295
    simpa using h
  have hprev := st205_p295
  have hstep := st205_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p297 : ((1675582342973/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT205 (i+1))
      = (∑ i ∈ Finset.range 296, stT205 (i+1)) + stT205 297 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 296
    simpa using h
  have hprev := st205_p296
  have hstep := st205_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p298 : ((895608131727/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT205 (i+1))
      = (∑ i ∈ Finset.range 297, stT205 (i+1)) + stT205 298 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 297
    simpa using h
  have hprev := st205_p297
  have hstep := st205_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p299 : ((1935667245217/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT205 (i+1))
      = (∑ i ∈ Finset.range 298, stT205 (i+1)) + stT205 299 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 298
    simpa using h
  have hprev := st205_p298
  have hstep := st205_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p300 : ((4087342198709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT205 (i+1))
      = (∑ i ∈ Finset.range 299, stT205 (i+1)) + stT205 300 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 299
    simpa using h
  have hprev := st205_p299
  have hstep := st205_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p301 : ((4134190025129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT205 (i+1))
      = (∑ i ∈ Finset.range 300, stT205 (i+1)) + stT205 301 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 300
    simpa using h
  have hprev := st205_p300
  have hstep := st205_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p302 : ((798412157149/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT205 (i+1))
      = (∑ i ∈ Finset.range 301, stT205 (i+1)) + stT205 302 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 301
    simpa using h
  have hprev := st205_p301
  have hstep := st205_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p303 : ((59598762809/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT205 (i+1))
      = (∑ i ∈ Finset.range 302, stT205 (i+1)) + stT205 303 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 302
    simpa using h
  have hprev := st205_p302
  have hstep := st205_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p304 : ((1380343437581/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT205 (i+1))
      = (∑ i ∈ Finset.range 303, stT205 (i+1)) + stT205 304 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 303
    simpa using h
  have hprev := st205_p303
  have hstep := st205_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p305 : ((1315805804291/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT205 (i+1))
      = (∑ i ∈ Finset.range 304, stT205 (i+1)) + stT205 305 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 304
    simpa using h
  have hprev := st205_p304
  have hstep := st205_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p306 : ((827546228749/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT205 (i+1))
      = (∑ i ∈ Finset.range 305, stT205 (i+1)) + stT205 306 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 305
    simpa using h
  have hprev := st205_p305
  have hstep := st205_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p307 : ((1751427401023/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT205 (i+1))
      = (∑ i ∈ Finset.range 306, stT205 (i+1)) + stT205 307 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 306
    simpa using h
  have hprev := st205_p306
  have hstep := st205_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p308 : ((1891985588581/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT205 (i+1))
      = (∑ i ∈ Finset.range 307, stT205 (i+1)) + stT205 308 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 307
    simpa using h
  have hprev := st205_p307
  have hstep := st205_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p309 : ((2016676689141/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT205 (i+1))
      = (∑ i ∈ Finset.range 308, stT205 (i+1)) + stT205 309 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 308
    simpa using h
  have hprev := st205_p308
  have hstep := st205_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p310 : ((259106500971/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT205 (i+1))
      = (∑ i ∈ Finset.range 309, stT205 (i+1)) + stT205 310 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 309
    simpa using h
  have hprev := st205_p309
  have hstep := st205_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p311 : ((1018650254061/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT205 (i+1))
      = (∑ i ∈ Finset.range 310, stT205 (i+1)) + stT205 311 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 310
    simpa using h
  have hprev := st205_p310
  have hstep := st205_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p312 : ((7701674248239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT205 (i+1))
      = (∑ i ∈ Finset.range 311, stT205 (i+1)) + stT205 312 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 311
    simpa using h
  have hprev := st205_p311
  have hstep := st205_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p313 : ((7136414812709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT205 (i+1))
      = (∑ i ∈ Finset.range 312, stT205 (i+1)) + stT205 313 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 312
    simpa using h
  have hprev := st205_p312
  have hstep := st205_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p314 : ((6687349085291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT205 (i+1))
      = (∑ i ∈ Finset.range 313, stT205 (i+1)) + stT205 314 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 313
    simpa using h
  have hprev := st205_p313
  have hstep := st205_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p315 : ((408621793363/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT205 (i+1))
      = (∑ i ∈ Finset.range 314, stT205 (i+1)) + stT205 315 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 314
    simpa using h
  have hprev := st205_p314
  have hstep := st205_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p316 : ((6747336761639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT205 (i+1))
      = (∑ i ∈ Finset.range 315, stT205 (i+1)) + stT205 316 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 315
    simpa using h
  have hprev := st205_p315
  have hstep := st205_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p317 : ((7228568382189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT205 (i+1))
      = (∑ i ∈ Finset.range 316, stT205 (i+1)) + stT205 317 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 316
    simpa using h
  have hprev := st205_p316
  have hstep := st205_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p318 : ((7786281370929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT205 (i+1))
      = (∑ i ∈ Finset.range 317, stT205 (i+1)) + stT205 318 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 317
    simpa using h
  have hprev := st205_p317
  have hstep := st205_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p319 : ((8196804823277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT205 (i+1))
      = (∑ i ∈ Finset.range 318, stT205 (i+1)) + stT205 319 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 318
    simpa using h
  have hprev := st205_p318
  have hstep := st205_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p320 : ((1659537305537/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT205 (i+1))
      = (∑ i ∈ Finset.range 319, stT205 (i+1)) + stT205 320 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 319
    simpa using h
  have hprev := st205_p319
  have hstep := st205_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p321 : ((8050805156381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT205 (i+1))
      = (∑ i ∈ Finset.range 320, stT205 (i+1)) + stT205 321 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 320
    simpa using h
  have hprev := st205_p320
  have hstep := st205_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p322 : ((7555201337869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT205 (i+1))
      = (∑ i ∈ Finset.range 321, stT205 (i+1)) + stT205 322 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 321
    simpa using h
  have hprev := st205_p321
  have hstep := st205_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p323 : ((7005921803829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT205 (i+1))
      = (∑ i ∈ Finset.range 322, stT205 (i+1)) + stT205 323 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 322
    simpa using h
  have hprev := st205_p322
  have hstep := st205_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p324 : ((1323316076249/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT205 (i+1))
      = (∑ i ∈ Finset.range 323, stT205 (i+1)) + stT205 324 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 323
    simpa using h
  have hprev := st205_p323
  have hstep := st205_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p325 : ((326827267373/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT205 (i+1))
      = (∑ i ∈ Finset.range 324, stT205 (i+1)) + stT205 325 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 324
    simpa using h
  have hprev := st205_p324
  have hstep := st205_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p326 : ((1698688982809/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT205 (i+1))
      = (∑ i ∈ Finset.range 325, stT205 (i+1)) + stT205 326 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 325
    simpa using h
  have hprev := st205_p325
  have hstep := st205_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p327 : ((3645385089093/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT205 (i+1))
      = (∑ i ∈ Finset.range 326, stT205 (i+1)) + stT205 327 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 326
    simpa using h
  have hprev := st205_p326
  have hstep := st205_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p328 : ((7835115813107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT205 (i+1))
      = (∑ i ∈ Finset.range 327, stT205 (i+1)) + stT205 328 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 327
    simpa using h
  have hprev := st205_p327
  have hstep := st205_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p329 : ((411114432569/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT205 (i+1))
      = (∑ i ∈ Finset.range 328, stT205 (i+1)) + stT205 329 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 328
    simpa using h
  have hprev := st205_p328
  have hstep := st205_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p330 : ((8308057444547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT205 (i+1))
      = (∑ i ∈ Finset.range 329, stT205 (i+1)) + stT205 330 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 329
    simpa using h
  have hprev := st205_p329
  have hstep := st205_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p331 : ((8062157226147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT205 (i+1))
      = (∑ i ∈ Finset.range 330, stT205 (i+1)) + stT205 331 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 330
    simpa using h
  have hprev := st205_p330
  have hstep := st205_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p332 : ((7577529837843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT205 (i+1))
      = (∑ i ∈ Finset.range 331, stT205 (i+1)) + stT205 332 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 331
    simpa using h
  have hprev := st205_p331
  have hstep := st205_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p333 : ((7033982573483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT205 (i+1))
      = (∑ i ∈ Finset.range 332, stT205 (i+1)) + stT205 333 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 332
    simpa using h
  have hprev := st205_p332
  have hstep := st205_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p334 : ((6630847372427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT205 (i+1))
      = (∑ i ∈ Finset.range 333, stT205 (i+1)) + stT205 334 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 333
    simpa using h
  have hprev := st205_p333
  have hstep := st205_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p335 : ((50891293257/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT205 (i+1))
      = (∑ i ∈ Finset.range 334, stT205 (i+1)) + stT205 335 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 334
    simpa using h
  have hprev := st205_p334
  have hstep := st205_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p336 : ((840542888049/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT205 (i+1))
      = (∑ i ∈ Finset.range 335, stT205 (i+1)) + stT205 336 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 335
    simpa using h
  have hprev := st205_p335
  have hstep := st205_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p337 : ((3592068638253/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT205 (i+1))
      = (∑ i ∈ Finset.range 336, stT205 (i+1)) + stT205 337 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 336
    simpa using h
  have hprev := st205_p336
  have hstep := st205_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p338 : ((772756921417/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT205 (i+1))
      = (∑ i ∈ Finset.range 337, stT205 (i+1)) + stT205 338 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 337
    simpa using h
  have hprev := st205_p337
  have hstep := st205_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p339 : ((1632169762459/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT205 (i+1))
      = (∑ i ∈ Finset.range 338, stT205 (i+1)) + stT205 339 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 338
    simpa using h
  have hprev := st205_p338
  have hstep := st205_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p340 : ((8331324109461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT205 (i+1))
      = (∑ i ∈ Finset.range 339, stT205 (i+1)) + stT205 340 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 339
    simpa using h
  have hprev := st205_p339
  have hstep := st205_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p341 : ((2045120568501/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT205 (i+1))
      = (∑ i ∈ Finset.range 340, stT205 (i+1)) + stT205 341 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 340
    simpa using h
  have hprev := st205_p340
  have hstep := st205_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p342 : ((3881408275941/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT205 (i+1))
      = (∑ i ∈ Finset.range 341, stT205 (i+1)) + stT205 342 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 341
    simpa using h
  have hprev := st205_p341
  have hstep := st205_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p343 : ((451563235827/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT205 (i+1))
      = (∑ i ∈ Finset.range 342, stT205 (i+1)) + stT205 343 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 342
    simpa using h
  have hprev := st205_p342
  have hstep := st205_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p344 : ((844207842853/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT205 (i+1))
      = (∑ i ∈ Finset.range 343, stT205 (i+1)) + stT205 344 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 343
    simpa using h
  have hprev := st205_p343
  have hstep := st205_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p345 : ((813807026459/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT205 (i+1))
      = (∑ i ∈ Finset.range 344, stT205 (i+1)) + stT205 345 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 344
    simpa using h
  have hprev := st205_p344
  have hstep := st205_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p346 : ((6577282952587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT205 (i+1))
      = (∑ i ∈ Finset.range 345, stT205 (i+1)) + stT205 346 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 345
    simpa using h
  have hprev := st205_p345
  have hstep := st205_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p347 : ((6929739523299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT205 (i+1))
      = (∑ i ∈ Finset.range 346, stT205 (i+1)) + stT205 347 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 346
    simpa using h
  have hprev := st205_p346
  have hstep := st205_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p348 : ((7447118260147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT205 (i+1))
      = (∑ i ∈ Finset.range 347, stT205 (i+1)) + stT205 348 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 347
    simpa using h
  have hprev := st205_p347
  have hstep := st205_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p349 : ((39772902533/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT205 (i+1))
      = (∑ i ∈ Finset.range 348, stT205 (i+1)) + stT205 349 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 348
    simpa using h
  have hprev := st205_p348
  have hstep := st205_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p350 : ((1035314520983/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT205 (i+1))
      = (∑ i ∈ Finset.range 349, stT205 (i+1)) + stT205 350 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 349
    simpa using h
  have hprev := st205_p349
  have hstep := st205_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p351 : ((1040355617303/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT205 (i+1))
      = (∑ i ∈ Finset.range 350, stT205 (i+1)) + stT205 351 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 350
    simpa using h
  have hprev := st205_p350
  have hstep := st205_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p352 : ((806377025529/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT205 (i+1))
      = (∑ i ∈ Finset.range 351, stT205 (i+1)) + stT205 352 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 351
    simpa using h
  have hprev := st205_p351
  have hstep := st205_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p353 : ((3796031579029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT205 (i+1))
      = (∑ i ∈ Finset.range 352, stT205 (i+1)) + stT205 353 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 352
    simpa using h
  have hprev := st205_p352
  have hstep := st205_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p354 : ((882887923651/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT205 (i+1))
      = (∑ i ∈ Finset.range 353, stT205 (i+1)) + stT205 354 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 353
    simpa using h
  have hprev := st205_p353
  have hstep := st205_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p355 : ((6649213046603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT205 (i+1))
      = (∑ i ∈ Finset.range 354, stT205 (i+1)) + stT205 355 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 354
    simpa using h
  have hprev := st205_p354
  have hstep := st205_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p356 : ((3241825184493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT205 (i+1))
      = (∑ i ∈ Finset.range 355, stT205 (i+1)) + stT205 356 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 355
    simpa using h
  have hprev := st205_p355
  have hstep := st205_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p357 : ((3309171687353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT205 (i+1))
      = (∑ i ∈ Finset.range 356, stT205 (i+1)) + stT205 357 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 356
    simpa using h
  have hprev := st205_p356
  have hstep := st205_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p358 : ((3504305872487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT205 (i+1))
      = (∑ i ∈ Finset.range 357, stT205 (i+1)) + stT205 358 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 357
    simpa using h
  have hprev := st205_p357
  have hstep := st205_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p359 : ((7528918977671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT205 (i+1))
      = (∑ i ∈ Finset.range 358, stT205 (i+1)) + stT205 359 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 358
    simpa using h
  have hprev := st205_p358
  have hstep := st205_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p360 : ((8013905652779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT205 (i+1))
      = (∑ i ∈ Finset.range 359, stT205 (i+1)) + stT205 360 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 359
    simpa using h
  have hprev := st205_p359
  have hstep := st205_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p361 : ((8311087312269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT205 (i+1))
      = (∑ i ∈ Finset.range 360, stT205 (i+1)) + stT205 361 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 360
    simpa using h
  have hprev := st205_p360
  have hstep := st205_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p362 : ((1665677618493/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT205 (i+1))
      = (∑ i ∈ Finset.range 361, stT205 (i+1)) + stT205 362 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 361
    simpa using h
  have hprev := st205_p361
  have hstep := st205_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p363 : ((8061876324593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT205 (i+1))
      = (∑ i ∈ Finset.range 362, stT205 (i+1)) + stT205 363 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 362
    simpa using h
  have hprev := st205_p362
  have hstep := st205_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p364 : ((7595566214927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT205 (i+1))
      = (∑ i ∈ Finset.range 363, stT205 (i+1)) + stT205 364 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 363
    simpa using h
  have hprev := st205_p363
  have hstep := st205_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p365 : ((7074146928847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT205 (i+1))
      = (∑ i ∈ Finset.range 364, stT205 (i+1)) + stT205 365 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 364
    simpa using h
  have hprev := st205_p364
  have hstep := st205_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p366 : ((3328841618739/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT205 (i+1))
      = (∑ i ∈ Finset.range 365, stT205 (i+1)) + stT205 366 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 365
    simpa using h
  have hprev := st205_p365
  have hstep := st205_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p367 : ((647257144997/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT205 (i+1))
      = (∑ i ∈ Finset.range 366, stT205 (i+1)) + stT205 367 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 366
    simpa using h
  have hprev := st205_p366
  have hstep := st205_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p368 : ((205429408531/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT205 (i+1))
      = (∑ i ∈ Finset.range 367, stT205 (i+1)) + stT205 368 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 367
    simpa using h
  have hprev := st205_p367
  have hstep := st205_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p369 : ((3464599851149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT205 (i+1))
      = (∑ i ∈ Finset.range 368, stT205 (i+1)) + stT205 369 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 368
    simpa using h
  have hprev := st205_p368
  have hstep := st205_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p370 : ((3715497764649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT205 (i+1))
      = (∑ i ∈ Finset.range 369, stT205 (i+1)) + stT205 370 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 369
    simpa using h
  have hprev := st205_p369
  have hstep := st205_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p371 : ((396430749117/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT205 (i+1))
      = (∑ i ∈ Finset.range 370, stT205 (i+1)) + stT205 371 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 370
    simpa using h
  have hprev := st205_p370
  have hstep := st205_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p372 : ((206858508351/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT205 (i+1))
      = (∑ i ∈ Finset.range 371, stT205 (i+1)) + stT205 372 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 371
    simpa using h
  have hprev := st205_p371
  have hstep := st205_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p373 : ((418341646439/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT205 (i+1))
      = (∑ i ∈ Finset.range 372, stT205 (i+1)) + stT205 373 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 372
    simpa using h
  have hprev := st205_p372
  have hstep := st205_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p374 : ((2045051511227/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT205 (i+1))
      = (∑ i ∈ Finset.range 373, stT205 (i+1)) + stT205 374 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 373
    simpa using h
  have hprev := st205_p373
  have hstep := st205_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p375 : ((15176554083/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT205 (i+1))
      = (∑ i ∈ Finset.range 374, stT205 (i+1)) + stT205 375 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 374
    simpa using h
  have hprev := st205_p374
  have hstep := st205_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p376 : ((7257677361429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT205 (i+1))
      = (∑ i ∈ Finset.range 375, stT205 (i+1)) + stT205 376 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 375
    simpa using h
  have hprev := st205_p375
  have hstep := st205_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p377 : ((3395428186801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT205 (i+1))
      = (∑ i ∈ Finset.range 376, stT205 (i+1)) + stT205 377 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 376
    simpa using h
  have hprev := st205_p376
  have hstep := st205_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p378 : ((6504019025727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT205 (i+1))
      = (∑ i ∈ Finset.range 377, stT205 (i+1)) + stT205 378 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 377
    simpa using h
  have hprev := st205_p377
  have hstep := st205_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p379 : ((6478376819007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT205 (i+1))
      = (∑ i ∈ Finset.range 378, stT205 (i+1)) + stT205 379 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 378
    simpa using h
  have hprev := st205_p378
  have hstep := st205_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p380 : ((6719905377921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT205 (i+1))
      = (∑ i ∈ Finset.range 379, stT205 (i+1)) + stT205 380 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 379
    simpa using h
  have hprev := st205_p379
  have hstep := st205_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p381 : ((894854355047/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT205 (i+1))
      = (∑ i ∈ Finset.range 380, stT205 (i+1)) + stT205 381 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 380
    simpa using h
  have hprev := st205_p380
  have hstep := st205_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p382 : ((958806017717/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT205 (i+1))
      = (∑ i ∈ Finset.range 381, stT205 (i+1)) + stT205 382 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 381
    simpa using h
  have hprev := st205_p381
  have hstep := st205_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p383 : ((202772404209/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT205 (i+1))
      = (∑ i ∈ Finset.range 382, stT205 (i+1)) + stT205 383 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 382
    simpa using h
  have hprev := st205_p382
  have hstep := st205_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p384 : ((208940623241/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT205 (i+1))
      = (∑ i ∈ Finset.range 383, stT205 (i+1)) + stT205 384 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 383
    simpa using h
  have hprev := st205_p383
  have hstep := st205_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p385 : ((1042886348497/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT205 (i+1))
      = (∑ i ∈ Finset.range 384, stT205 (i+1)) + stT205 385 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 384
    simpa using h
  have hprev := st205_p384
  have hstep := st205_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p386 : ((8072594227709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT205 (i+1))
      = (∑ i ∈ Finset.range 385, stT205 (i+1)) + stT205 386 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 385
    simpa using h
  have hprev := st205_p385
  have hstep := st205_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p387 : ((7621720637921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT205 (i+1))
      = (∑ i ∈ Finset.range 386, stT205 (i+1)) + stT205 387 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 386
    simpa using h
  have hprev := st205_p386
  have hstep := st205_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p388 : ((7114627924651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT205 (i+1))
      = (∑ i ∈ Finset.range 387, stT205 (i+1)) + stT205 388 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 387
    simpa using h
  have hprev := st205_p387
  have hstep := st205_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p389 : ((1672386013339/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT205 (i+1))
      = (∑ i ∈ Finset.range 388, stT205 (i+1)) + stT205 389 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 388
    simpa using h
  have hprev := st205_p388
  have hstep := st205_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p390 : ((1615282162069/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT205 (i+1))
      = (∑ i ∈ Finset.range 389, stT205 (i+1)) + stT205 390 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 389
    simpa using h
  have hprev := st205_p389
  have hstep := st205_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p391 : ((1297986802143/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT205 (i+1))
      = (∑ i ∈ Finset.range 390, stT205 (i+1)) + stT205 391 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 390
    simpa using h
  have hprev := st205_p390
  have hstep := st205_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p392 : ((6766986379451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT205 (i+1))
      = (∑ i ∈ Finset.range 391, stT205 (i+1)) + stT205 392 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 391
    simpa using h
  have hprev := st205_p391
  have hstep := st205_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p393 : ((112768645881/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT205 (i+1))
      = (∑ i ∈ Finset.range 392, stT205 (i+1)) + stT205 393 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 392
    simpa using h
  have hprev := st205_p392
  have hstep := st205_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p394 : ((48251554953/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT205 (i+1))
      = (∑ i ∈ Finset.range 393, stT205 (i+1)) + stT205 394 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 393
    simpa using h
  have hprev := st205_p393
  have hstep := st205_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p395 : ((407153712819/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT205 (i+1))
      = (∑ i ∈ Finset.range 394, stT205 (i+1)) + stT205 395 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 394
    simpa using h
  have hprev := st205_p394
  have hstep := st205_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p396 : ((837495867489/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT205 (i+1))
      = (∑ i ∈ Finset.range 395, stT205 (i+1)) + stT205 396 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 395
    simpa using h
  have hprev := st205_p395
  have hstep := st205_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p397 : ((4178101095649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT205 (i+1))
      = (∑ i ∈ Finset.range 396, stT205 (i+1)) + stT205 397 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 396
    simpa using h
  have hprev := st205_p396
  have hstep := st205_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p398 : ((4046433437269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT205 (i+1))
      = (∑ i ∈ Finset.range 397, stT205 (i+1)) + stT205 398 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 397
    simpa using h
  have hprev := st205_p397
  have hstep := st205_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p399 : ((239196706053/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT205 (i+1))
      = (∑ i ∈ Finset.range 398, stT205 (i+1)) + stT205 399 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 398
    simpa using h
  have hprev := st205_p398
  have hstep := st205_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p400 : ((3577146296847/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT205 (i+1))
      = (∑ i ∈ Finset.range 399, stT205 (i+1)) + stT205 400 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 399
    simpa using h
  have hprev := st205_p399
  have hstep := st205_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p401 : ((6721321249023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT205 (i+1))
      = (∑ i ∈ Finset.range 400, stT205 (i+1)) + stT205 401 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 400
    simpa using h
  have hprev := st205_p400
  have hstep := st205_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p402 : ((6465500831933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT205 (i+1))
      = (∑ i ∈ Finset.range 401, stT205 (i+1)) + stT205 402 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 401
    simpa using h
  have hprev := st205_p401
  have hstep := st205_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p403 : ((6450932346477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT205 (i+1))
      = (∑ i ∈ Finset.range 402, stT205 (i+1)) + stT205 403 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 402
    simpa using h
  have hprev := st205_p402
  have hstep := st205_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p404 : ((6680143864257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT205 (i+1))
      = (∑ i ∈ Finset.range 403, stT205 (i+1)) + stT205 404 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 403
    simpa using h
  have hprev := st205_p403
  have hstep := st205_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p405 : ((3547176878853/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT205 (i+1))
      = (∑ i ∈ Finset.range 404, stT205 (i+1)) + stT205 405 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 404
    simpa using h
  have hprev := st205_p404
  have hstep := st205_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p406 : ((151780973717/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT205 (i+1))
      = (∑ i ∈ Finset.range 405, stT205 (i+1)) + stT205 406 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 405
    simpa using h
  have hprev := st205_p405
  have hstep := st205_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p407 : ((50254178761/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT205 (i+1))
      = (∑ i ∈ Finset.range 406, stT205 (i+1)) + stT205 407 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 406
    simpa using h
  have hprev := st205_p406
  have hstep := st205_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p408 : ((1667499409001/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT205 (i+1))
      = (∑ i ∈ Finset.range 407, stT205 (i+1)) + stT205 408 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 407
    simpa using h
  have hprev := st205_p407
  have hstep := st205_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p409 : ((8407049408353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT205 (i+1))
      = (∑ i ∈ Finset.range 408, stT205 (i+1)) + stT205 409 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 408
    simpa using h
  have hprev := st205_p408
  have hstep := st205_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p410 : ((4116656073069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT205 (i+1))
      = (∑ i ∈ Finset.range 409, stT205 (i+1)) + stT205 410 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 409
    simpa using h
  have hprev := st205_p409
  have hstep := st205_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p411 : ((3929923833541/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT205 (i+1))
      = (∑ i ∈ Finset.range 410, stT205 (i+1)) + stT205 411 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 410
    simpa using h
  have hprev := st205_p410
  have hstep := st205_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p412 : ((7378374537887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT205 (i+1))
      = (∑ i ∈ Finset.range 411, stT205 (i+1)) + stT205 412 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 411
    simpa using h
  have hprev := st205_p411
  have hstep := st205_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p413 : ((6905878050519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT205 (i+1))
      = (∑ i ∈ Finset.range 412, stT205 (i+1)) + stT205 413 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 412
    simpa using h
  have hprev := st205_p412
  have hstep := st205_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p414 : ((6556091089979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT205 (i+1))
      = (∑ i ∈ Finset.range 413, stT205 (i+1)) + stT205 414 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 413
    simpa using h
  have hprev := st205_p413
  have hstep := st205_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p415 : ((6412279646933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT205 (i+1))
      = (∑ i ∈ Finset.range 414, stT205 (i+1)) + stT205 415 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 414
    simpa using h
  have hprev := st205_p414
  have hstep := st205_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p416 : ((6507785197193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT205 (i+1))
      = (∑ i ∈ Finset.range 415, stT205 (i+1)) + stT205 416 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 415
    simpa using h
  have hprev := st205_p415
  have hstep := st205_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p417 : ((6818833134149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT205 (i+1))
      = (∑ i ∈ Finset.range 416, stT205 (i+1)) + stT205 417 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 416
    simpa using h
  have hprev := st205_p416
  have hstep := st205_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p418 : ((7270920172189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT205 (i+1))
      = (∑ i ∈ Finset.range 417, stT205 (i+1)) + stT205 418 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 417
    simpa using h
  have hprev := st205_p417
  have hstep := st205_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p419 : ((1551413037357/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT205 (i+1))
      = (∑ i ∈ Finset.range 418, stT205 (i+1)) + stT205 419 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 418
    simpa using h
  have hprev := st205_p418
  have hstep := st205_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p420 : ((1632659542467/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT205 (i+1))
      = (∑ i ∈ Finset.range 419, stT205 (i+1)) + stT205 420 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 419
    simpa using h
  have hprev := st205_p419
  have hstep := st205_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p421 : ((1679063989647/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT205 (i+1))
      = (∑ i ∈ Finset.range 420, stT205 (i+1)) + stT205 421 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 420
    simpa using h
  have hprev := st205_p420
  have hstep := st205_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p422 : ((8400102192843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT205 (i+1))
      = (∑ i ∈ Finset.range 421, stT205 (i+1)) + stT205 422 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 421
    simpa using h
  have hprev := st205_p421
  have hstep := st205_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p423 : ((4088786899901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT205 (i+1))
      = (∑ i ∈ Finset.range 422, stT205 (i+1)) + stT205 423 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 422
    simpa using h
  have hprev := st205_p422
  have hstep := st205_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p424 : ((1944971400883/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT205 (i+1))
      = (∑ i ∈ Finset.range 423, stT205 (i+1)) + stT205 424 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 423
    simpa using h
  have hprev := st205_p423
  have hstep := st205_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p425 : ((14597576567/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT205 (i+1))
      = (∑ i ∈ Finset.range 424, stT205 (i+1)) + stT205 425 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 424
    simpa using h
  have hprev := st205_p424
  have hstep := st205_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p426 : ((855523354991/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT205 (i+1))
      = (∑ i ∈ Finset.range 425, stT205 (i+1)) + stT205 426 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 425
    simpa using h
  have hprev := st205_p425
  have hstep := st205_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p427 : ((407436570479/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT205 (i+1))
      = (∑ i ∈ Finset.range 426, stT205 (i+1)) + stT205 427 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 426
    simpa using h
  have hprev := st205_p426
  have hstep := st205_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p428 : ((6395949832511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT205 (i+1))
      = (∑ i ∈ Finset.range 427, stT205 (i+1)) + stT205 428 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 427
    simpa using h
  have hprev := st205_p427
  have hstep := st205_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p429 : ((6501811368767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT205 (i+1))
      = (∑ i ∈ Finset.range 428, stT205 (i+1)) + stT205 429 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 428
    simpa using h
  have hprev := st205_p428
  have hstep := st205_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p430 : ((6811870309393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT205 (i+1))
      = (∑ i ∈ Finset.range 429, stT205 (i+1)) + stT205 430 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 429
    simpa using h
  have hprev := st205_p429
  have hstep := st205_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p431 : ((7256213243233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT205 (i+1))
      = (∑ i ∈ Finset.range 430, stT205 (i+1)) + stT205 431 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 430
    simpa using h
  have hprev := st205_p430
  have hstep := st205_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p432 : ((3867909184679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT205 (i+1))
      = (∑ i ∈ Finset.range 431, stT205 (i+1)) + stT205 432 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 431
    simpa using h
  have hprev := st205_p431
  have hstep := st205_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p433 : ((2036191562253/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT205 (i+1))
      = (∑ i ∈ Finset.range 432, stT205 (i+1)) + stT205 433 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 432
    simpa using h
  have hprev := st205_p432
  have hstep := st205_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p434 : ((65575002069/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT205 (i+1))
      = (∑ i ∈ Finset.range 433, stT205 (i+1)) + stT205 434 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 433
    simpa using h
  have hprev := st205_p433
  have hstep := st205_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p435 : ((1685729897919/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT205 (i+1))
      = (∑ i ∈ Finset.range 434, stT205 (i+1)) + stT205 435 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 434
    simpa using h
  have hprev := st205_p434
  have hstep := st205_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p436 : ((8243228835129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT205 (i+1))
      = (∑ i ∈ Finset.range 435, stT205 (i+1)) + stT205 436 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 435
    simpa using h
  have hprev := st205_p435
  have hstep := st205_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p437 : ((3939230346657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT205 (i+1))
      = (∑ i ∈ Finset.range 436, stT205 (i+1)) + stT205 437 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 436
    simpa using h
  have hprev := st205_p436
  have hstep := st205_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p438 : ((7413758302683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT205 (i+1))
      = (∑ i ∈ Finset.range 437, stT205 (i+1)) + stT205 438 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 437
    simpa using h
  have hprev := st205_p437
  have hstep := st205_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p439 : ((6949295291391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT205 (i+1))
      = (∑ i ∈ Finset.range 438, stT205 (i+1)) + stT205 439 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 438
    simpa using h
  have hprev := st205_p438
  have hstep := st205_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p440 : ((6584300214283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT205 (i+1))
      = (∑ i ∈ Finset.range 439, stT205 (i+1)) + stT205 440 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 439
    simpa using h
  have hprev := st205_p439
  have hstep := st205_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p441 : ((1598992025589/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT205 (i+1))
      = (∑ i ∈ Finset.range 440, stT205 (i+1)) + stT205 441 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 440
    simpa using h
  have hprev := st205_p440
  have hstep := st205_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p442 : ((1605851864311/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT205 (i+1))
      = (∑ i ∈ Finset.range 441, stT205 (i+1)) + stT205 442 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 441
    simpa using h
  have hprev := st205_p441
  have hstep := st205_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p443 : ((3329945587359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT205 (i+1))
      = (∑ i ∈ Finset.range 442, stT205 (i+1)) + stT205 443 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 442
    simpa using h
  have hprev := st205_p442
  have hstep := st205_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p444 : ((3527434577967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT205 (i+1))
      = (∑ i ∈ Finset.range 443, stT205 (i+1)) + stT205 444 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 443
    simpa using h
  have hprev := st205_p443
  have hstep := st205_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p445 : ((1881278315781/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT205 (i+1))
      = (∑ i ∈ Finset.range 444, stT205 (i+1)) + stT205 445 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 444
    simpa using h
  have hprev := st205_p444
  have hstep := st205_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p446 : ((7972460408257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT205 (i+1))
      = (∑ i ∈ Finset.range 445, stT205 (i+1)) + stT205 446 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 445
    simpa using h
  have hprev := st205_p445
  have hstep := st205_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p447 : ((830434832251/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT205 (i+1))
      = (∑ i ∈ Finset.range 446, stT205 (i+1)) + stT205 447 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 446
    simpa using h
  have hprev := st205_p446
  have hstep := st205_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p448 : ((845282014099/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT205 (i+1))
      = (∑ i ∈ Finset.range 447, stT205 (i+1)) + stT205 448 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 447
    simpa using h
  have hprev := st205_p447
  have hstep := st205_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p449 : ((419409206813/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT205 (i+1))
      = (∑ i ∈ Finset.range 448, stT205 (i+1)) + stT205 449 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 448
    simpa using h
  have hprev := st205_p448
  have hstep := st205_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p450 : ((812455654687/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT205 (i+1))
      = (∑ i ∈ Finset.range 449, stT205 (i+1)) + stT205 450 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 449
    simpa using h
  have hprev := st205_p449
  have hstep := st205_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p451 : ((1929109719883/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT205 (i+1))
      = (∑ i ∈ Finset.range 450, stT205 (i+1)) + stT205 451 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 450
    simpa using h
  have hprev := st205_p450
  have hstep := st205_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p452 : ((7247150772973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT205 (i+1))
      = (∑ i ∈ Finset.range 451, stT205 (i+1)) + stT205 452 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 451
    simpa using h
  have hprev := st205_p451
  have hstep := st205_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p453 : ((13303976341/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT205 (i+1))
      = (∑ i ∈ Finset.range 452, stT205 (i+1)) + stT205 453 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 452
    simpa using h
  have hprev := st205_p452
  have hstep := st205_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p454 : ((1624307878769/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT205 (i+1))
      = (∑ i ∈ Finset.range 453, stT205 (i+1)) + stT205 454 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 453
    simpa using h
  have hprev := st205_p453
  have hstep := st205_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p455 : ((1591579689077/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT205 (i+1))
      = (∑ i ∈ Finset.range 454, stT205 (i+1)) + stT205 455 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 454
    simpa using h
  have hprev := st205_p454
  have hstep := st205_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p456 : ((1611045885079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT205 (i+1))
      = (∑ i ∈ Finset.range 455, stT205 (i+1)) + stT205 456 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 455
    simpa using h
  have hprev := st205_p455
  have hstep := st205_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p457 : ((1678622553329/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT205 (i+1))
      = (∑ i ∈ Finset.range 456, stT205 (i+1)) + stT205 457 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 456
    simpa using h
  have hprev := st205_p456
  have hstep := st205_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p458 : ((1424611335223/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT205 (i+1))
      = (∑ i ∈ Finset.range 457, stT205 (i+1)) + stT205 458 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 457
    simpa using h
  have hprev := st205_p457
  have hstep := st205_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p459 : ((1517793901343/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT205 (i+1))
      = (∑ i ∈ Finset.range 458, stT205 (i+1)) + stT205 459 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 458
    simpa using h
  have hprev := st205_p458
  have hstep := st205_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p460 : ((8020771078939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT205 (i+1))
      = (∑ i ∈ Finset.range 459, stT205 (i+1)) + stT205 460 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 459
    simpa using h
  have hprev := st205_p459
  have hstep := st205_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p461 : ((8334425393909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT205 (i+1))
      = (∑ i ∈ Finset.range 460, stT205 (i+1)) + stT205 461 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 460
    simpa using h
  have hprev := st205_p460
  have hstep := st205_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p462 : ((8469547488937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT205 (i+1))
      = (∑ i ∈ Finset.range 461, stT205 (i+1)) + stT205 462 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 461
    simpa using h
  have hprev := st205_p461
  have hstep := st205_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p463 : ((8400755279917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT205 (i+1))
      = (∑ i ∈ Finset.range 462, stT205 (i+1)) + stT205 463 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 462
    simpa using h
  have hprev := st205_p462
  have hstep := st205_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p464 : ((4071068276779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT205 (i+1))
      = (∑ i ∈ Finset.range 463, stT205 (i+1)) + stT205 464 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 463
    simpa using h
  have hprev := st205_p463
  have hstep := st205_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p465 : ((1936009488513/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT205 (i+1))
      = (∑ i ∈ Finset.range 464, stT205 (i+1)) + stT205 465 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 464
    simpa using h
  have hprev := st205_p464
  have hstep := st205_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p466 : ((5689849587/7812500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT205 (i+1))
      = (∑ i ∈ Finset.range 465, stT205 (i+1)) + stT205 466 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 465
    simpa using h
  have hprev := st205_p465
  have hstep := st205_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p467 : ((273876422707/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT205 (i+1))
      = (∑ i ∈ Finset.range 466, stT205 (i+1)) + stT205 467 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 466
    simpa using h
  have hprev := st205_p466
  have hstep := st205_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p468 : ((1629539760807/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT205 (i+1))
      = (∑ i ∈ Finset.range 467, stT205 (i+1)) + stT205 468 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 467
    simpa using h
  have hprev := st205_p467
  have hstep := st205_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p469 : ((158956467811/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT205 (i+1))
      = (∑ i ∈ Finset.range 468, stT205 (i+1)) + stT205 469 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 468
    simpa using h
  have hprev := st205_p468
  have hstep := st205_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p470 : ((159912762409/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT205 (i+1))
      = (∑ i ∈ Finset.range 469, stT205 (i+1)) + stT205 470 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 469
    simpa using h
  have hprev := st205_p469
  have hstep := st205_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p471 : ((331247491983/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT205 (i+1))
      = (∑ i ∈ Finset.range 470, stT205 (i+1)) + stT205 471 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 470
    simpa using h
  have hprev := st205_p470
  have hstep := st205_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p472 : ((3500141754609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT205 (i+1))
      = (∑ i ∈ Finset.range 471, stT205 (i+1)) + stT205 472 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 471
    simpa using h
  have hprev := st205_p471
  have hstep := st205_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p473 : ((3726175986109/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT205 (i+1))
      = (∑ i ∈ Finset.range 472, stT205 (i+1)) + stT205 473 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 472
    simpa using h
  have hprev := st205_p472
  have hstep := st205_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p474 : ((7897411212563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT205 (i+1))
      = (∑ i ∈ Finset.range 473, stT205 (i+1)) + stT205 474 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 473
    simpa using h
  have hprev := st205_p473
  have hstep := st205_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p475 : ((8253692566401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT205 (i+1))
      = (∑ i ∈ Finset.range 474, stT205 (i+1)) + stT205 475 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 474
    simpa using h
  have hprev := st205_p474
  have hstep := st205_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p476 : ((8456352493449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT205 (i+1))
      = (∑ i ∈ Finset.range 475, stT205 (i+1)) + stT205 476 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 475
    simpa using h
  have hprev := st205_p475
  have hstep := st205_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p477 : ((8469074813697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT205 (i+1))
      = (∑ i ∈ Finset.range 476, stT205 (i+1)) + stT205 477 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 476
    simpa using h
  have hprev := st205_p476
  have hstep := st205_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p478 : ((8290307591317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT205 (i+1))
      = (∑ i ∈ Finset.range 477, stT205 (i+1)) + stT205 478 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 477
    simpa using h
  have hprev := st205_p477
  have hstep := st205_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p479 : ((7953145829749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT205 (i+1))
      = (∑ i ∈ Finset.range 478, stT205 (i+1)) + stT205 479 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 478
    simpa using h
  have hprev := st205_p478
  have hstep := st205_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p480 : ((7518912246097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT205 (i+1))
      = (∑ i ∈ Finset.range 479, stT205 (i+1)) + stT205 480 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 479
    simpa using h
  have hprev := st205_p479
  have hstep := st205_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p481 : ((441615668881/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT205 (i+1))
      = (∑ i ∈ Finset.range 480, stT205 (i+1)) + stT205 481 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 480
    simpa using h
  have hprev := st205_p480
  have hstep := st205_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p482 : ((417182979413/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT205 (i+1))
      = (∑ i ∈ Finset.range 481, stT205 (i+1)) + stT205 482 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 481
    simpa using h
  have hprev := st205_p481
  have hstep := st205_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p483 : ((801925194967/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT205 (i+1))
      = (∑ i ∈ Finset.range 482, stT205 (i+1)) + stT205 483 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 482
    simpa using h
  have hprev := st205_p482
  have hstep := st205_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p484 : ((1583177410581/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT205 (i+1))
      = (∑ i ∈ Finset.range 483, stT205 (i+1)) + stT205 484 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 483
    simpa using h
  have hprev := st205_p483
  have hstep := st205_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p485 : ((322035717169/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT205 (i+1))
      = (∑ i ∈ Finset.range 484, stT205 (i+1)) + stT205 485 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 484
    simpa using h
  have hprev := st205_p484
  have hstep := st205_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p486 : ((1343938136503/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT205 (i+1))
      = (∑ i ∈ Finset.range 485, stT205 (i+1)) + stT205 486 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 485
    simpa using h
  have hprev := st205_p485
  have hstep := st205_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p487 : ((7120139495617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT205 (i+1))
      = (∑ i ∈ Finset.range 486, stT205 (i+1)) + stT205 487 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 486
    simpa using h
  have hprev := st205_p486
  have hstep := st205_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p488 : ((7571796254049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT205 (i+1))
      = (∑ i ∈ Finset.range 487, stT205 (i+1)) + stT205 488 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 487
    simpa using h
  have hprev := st205_p487
  have hstep := st205_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p489 : ((7996073411349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT205 (i+1))
      = (∑ i ∈ Finset.range 488, stT205 (i+1)) + stT205 489 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 488
    simpa using h
  have hprev := st205_p488
  have hstep := st205_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p490 : ((8319740883259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT205 (i+1))
      = (∑ i ∈ Finset.range 489, stT205 (i+1)) + stT205 490 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 489
    simpa using h
  have hprev := st205_p489
  have hstep := st205_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p491 : ((26523334643/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT205 (i+1))
      = (∑ i ∈ Finset.range 490, stT205 (i+1)) + stT205 491 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 490
    simpa using h
  have hprev := st205_p490
  have hstep := st205_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p492 : ((1694221346889/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT205 (i+1))
      = (∑ i ∈ Finset.range 491, stT205 (i+1)) + stT205 492 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 491
    simpa using h
  have hprev := st205_p491
  have hstep := st205_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p493 : ((8274180755457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT205 (i+1))
      = (∑ i ∈ Finset.range 492, stT205 (i+1)) + stT205 493 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 492
    simpa using h
  have hprev := st205_p492
  have hstep := st205_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p494 : ((7930882620783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT205 (i+1))
      = (∑ i ∈ Finset.range 493, stT205 (i+1)) + stT205 494 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 493
    simpa using h
  have hprev := st205_p493
  have hstep := st205_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p495 : ((3749975145731/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT205 (i+1))
      = (∑ i ∈ Finset.range 494, stT205 (i+1)) + stT205 495 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 494
    simpa using h
  have hprev := st205_p494
  have hstep := st205_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p496 : ((220451192239/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT205 (i+1))
      = (∑ i ∈ Finset.range 495, stT205 (i+1)) + stT205 496 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 495
    simpa using h
  have hprev := st205_p495
  have hstep := st205_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p497 : ((666928083891/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT205 (i+1))
      = (∑ i ∈ Finset.range 496, stT205 (i+1)) + stT205 497 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 496
    simpa using h
  have hprev := st205_p496
  have hstep := st205_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p498 : ((1281743099037/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT205 (i+1))
      = (∑ i ∈ Finset.range 497, stT205 (i+1)) + stT205 498 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 497
    simpa using h
  have hprev := st205_p497
  have hstep := st205_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p499 : ((6315702075473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT205 (i+1))
      = (∑ i ∈ Finset.range 498, stT205 (i+1)) + stT205 499 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 498
    simpa using h
  have hprev := st205_p498
  have hstep := st205_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_p500 : ((6405035555501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT205 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT205 (i+1))
      = (∑ i ∈ Finset.range 499, stT205 (i+1)) + stT205 500 := by
    have h := Finset.sum_range_succ (fun i => stT205 (i+1)) 499
    simpa using h
  have hprev := st205_p499
  have hstep := st205_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st205_s500 :
    |Real.sin (((205 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))
      - ((-195967/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -342409/1000000) (δ := 10359/1000000000) (ψ := -122331/1000000) 205 203
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 205`** (evaluated boundary). -/
theorem station_205_sign : hardyG ((((205:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 205 500 (by norm_num) (by norm_num)
    ((-122331/1000000 : ℚ) : ℝ)
  have hchain := st205_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT205 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((205 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-122331/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st205_c500
  have hsinb := abs_le.mp st205_s500
  have hbdy_lo : ((89780691686361/840505000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((205 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ))) / 2
          - ((((205:ℕ)):ℝ))
            * Real.sin (((205 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-122331/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((205:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((205:ℝ) * Real.log (500:ℝ) - ((-122331/1000000 : ℚ) : ℝ))) / 2
        - ((205:ℝ)) * Real.sin ((205:ℝ) * Real.log (500:ℝ) - ((-122331/1000000 : ℚ) : ℝ))
        ≥ ((200755997/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((205:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((200755997/1000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((200755997/1000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((200755997/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((205:ℕ)):ℝ))+1) * (((((205:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((1705745973847/5000000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((6405035555501/10000000000000 : ℚ) : ℝ) + ((89780691686361/840505000000000 : ℚ) : ℝ)
      - ((1705745973847/5000000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-122331/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((205:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-122331/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((205:ℕ)):ℝ)))).re
      - Real.sin ((-122331/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((205:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((205:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((205:ℕ)):ℝ))
      = (((((205:ℕ)):ℝ)) * (Real.log ((((205:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((205:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_205
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
  have hθwin : |(((-122331/1000000 : ℚ) : ℝ) + ((41:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((205:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((205:ℕ)):ℝ)))
    (φ := ((-122331/1000000 : ℚ) : ℝ) + ((41:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-122331/1000000 : ℚ) : ℝ) + ((41:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-122331/1000000 : ℚ)) : ℝ) - Real.pi) + ((41:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-122331/1000000 : ℚ)) : ℝ) - Real.pi) 41).1,
    (cos_sin_shift ((((-122331/1000000 : ℚ)) : ℝ) - Real.pi) 41).2]
  exact cos_sin_flip ((-122331/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_205_sign
end AxiomAudit
